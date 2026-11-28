import PEqualNP.Defs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def reads (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

theorem reads_le (g : Gate) : (reads g).length ≤ g.inputs.length := by
  cases h : g.op <;> simp [reads, h, Nat.min_le_right]

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  ((reads g).map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ reads g, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem eval_congr_reads (g : Gate) (w w' : List Bool)
    (h : ∀ a ∈ reads g, w.getD a false = w'.getD a false) :
    g.op.eval (g.inputs.map fun a => w.getD a false) =
      g.op.eval (g.inputs.map fun a => w'.getD a false) := by
  by_cases hn : g.op = .not
  · rw [hn]
    cases hi : g.inputs with
    | nil => simp [GateOp.eval, hi]
    | cons a l =>
      have ha := h a (by simp [reads, hn, hi])
      change (!w.getD a false) = !w'.getD a false
      rw [ha]
  · have he : g.inputs.map (fun a => w.getD a false) =
        g.inputs.map (fun a => w'.getD a false) := by
      apply List.map_congr_left
      intro a ha
      exact h a (by cases ho : g.op <;> simp_all [reads])
    rw [he]

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      apply eval_congr_reads
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ (reads g).toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) (le_trans (reads_le g) hg)) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ (reads g).toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem getD_take_eq (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD w false =
      (wiresFrom (C.gates.take k) (List.ofFn x)).getD w false := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  conv_lhs => rw [← List.take_append_drop k C.gates]
  rw [wiresFrom_append]
  apply getD_wiresFrom
  rw [length_wiresFrom]
  simpa [List.length_take, Nat.min_eq_left hk] using hw

theorem wire_support (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ k + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) →
        (C.wires (List.ofFn x)).getD w false =
          (C.wires (List.ofFn y)).getD w false := by
  let S := (suppsFrom (C.gates.take k) (inputSupps n)).getD w ∅
  refine ⟨S, ?_, ?_⟩
  · have hc := cnt_suppsFrom (C.gates.take k) 0 (inputSupps n)
      (fun g hg => hfan g (List.mem_of_mem_take hg)) cnt_inputs {w}
    simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add,
      List.length_take, Nat.min_eq_left hk] using hc
  · intro x y heq
    rw [getD_take_eq C n k w hk hw x, getD_take_eq C n k w hk hw y]
    exact (agree_wiresFrom x y (C.gates.take k) _ _ _ (agree_inputs x y)).2.2 w heq

theorem wire_essential_bound (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n + k)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (E : Finset (Fin n))
    (hsens : ∀ i ∈ E, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
        (C.wires (List.ofFn x)).getD w false ≠
          (C.wires (List.ofFn y)).getD w false) :
    E.card ≤ k + 1 := by
  obtain ⟨S, hcard, hdep⟩ := wire_support C n k w hk hw hfan
  apply le_trans (Finset.card_le_card (t := S) ?_) hcard
  intro i hi
  by_contra hni
  obtain ⟨x, y, hxy, hne⟩ := hsens i hi
  apply hne (hdep x y ?_)
  intro j hj
  apply hxy j
  intro hji
  subst j
  exact hni hj

def RO (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ Q : Finset (Fin n) → ((Fin n → Bool) → Bool) → Prop,
    (∀ i : Fin n, Q {i} (fun x => x i)) →
    (∀ A B a b, Disjoint A B → Q A a → Q B b →
      Q (A ∪ B) (fun x => a x && b x) ∧ Q (A ∪ B) (fun x => a x || b x)) → Q S f

theorem ro_leaf (i : Fin n) : RO {i} (fun x => x i) := fun _ hl _ => hl i

theorem ro_and {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b) :
    RO (A ∪ B) (fun x => a x && b x) :=
  fun Q hl hj => (hj A B a b hd (ha Q hl hj) (hb Q hl hj)).1

theorem ro_or {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b) :
    RO (A ∪ B) (fun x => a x || b x) :=
  fun Q hl hj => (hj A B a b hd (ha Q hl hj) (hb Q hl hj)).2

def Fam (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool) (W : Finset ℕ) : Prop :=
  (∀ w ∈ W, RO (L.getD w ∅) (F w)) ∧
  (∀ w ∈ W, ∀ v ∈ W, w ≠ v → Disjoint (L.getD w ∅) (L.getD v ∅))

def Tight (t : ℕ) (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card = t + W.card → Fam L F W

theorem tight_inputs : Tight 0 (inputSupps n) (fun j x => (List.ofFn x).getD j false) := by
  intro W heq
  have hvalid : ∀ j ∈ W, j < n := by
    intro j hj
    by_contra hn
    have hz : (inputSupps n).getD j ∅ = ∅ :=
      List.getD_eq_default _ _ (by simp [inputSupps]; omega)
    have he := heq
    rw [← Finset.insert_erase hj, Finset.biUnion_insert, hz, Finset.empty_union] at he
    rw [Finset.insert_erase hj] at he
    have hc := cnt_inputs (n := n) (W.erase j)
    have hcard := Finset.card_erase_add_one hj
    omega
  constructor
  · intro j hj
    have hv := hvalid j hj
    have hs : (inputSupps n).getD j ∅ = {⟨j, hv⟩} := by simp [inputSupps, hv]
    have hf : (fun x : Fin n → Bool => (List.ofFn x).getD j false) = (fun x => x ⟨j,hv⟩) := by
      funext x; simp [hv]
    rw [hs]
    change RO {⟨j,hv⟩} (fun x : Fin n → Bool => (List.ofFn x).getD j false)
    rw [hf]
    exact ro_leaf _
  · intro j hj k hk hne
    have hjn := hvalid j hj
    have hkn := hvalid k hk
    simpa [inputSupps, hjn, hkn, Fin.ext_iff] using hne

theorem union_step (L : List (Finset (Fin n))) (g : Gate) (W : Finset ℕ)
    (hW : L.length ∈ W) :
    (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
      ((W.erase L.length ∪ (reads g).toFinset).biUnion fun j => L.getD j ∅) := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_biUnion] at hi ⊢
    obtain ⟨j, hjW, hij⟩ := hi
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hij
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
      exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
    · rw [getD_snoc_ne _ _ _ _ hjl] at hij
      exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
  · intro hi
    obtain ⟨j,hj,hi⟩ := Finset.mem_biUnion.mp hi
    rcases Finset.mem_union.mp hj with hj | hj
    · refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_of_mem_erase hj, ?_⟩
      rw [getD_snoc_ne _ _ _ _ (Finset.ne_of_mem_erase hj)]
      exact hi
    · refine Finset.mem_biUnion.mpr ⟨L.length,hW,?_⟩
      rw [getD_snoc_eq]
      exact (mem_gateSupp L g i).mpr ⟨j,List.mem_toFinset.mp hj,hi⟩

theorem binary_of_reads (g : Gate)
    (ho : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hlen : g.inputs.length ≤ 2) (hcard : (reads g).toFinset.card = 2) :
    ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ (g.op = .and ∨ g.op = .or) := by
  have hn : g.op ≠ .not := by
    intro hn
    have hc := List.toFinset_card_le (reads g)
    have hl : (reads g).length ≤ 1 := by simp [reads,hn]
    omega
  have hop : g.op = .and ∨ g.op = .or := by rcases ho with h | h | h <;> simp_all
  have hr : reads g = g.inputs := by rcases hop with h | h <;> simp [reads,h]
  rw [hr] at hcard
  rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [hi] at hcard
  · simp [hi] at hcard
  · refine ⟨a,b,rfl,?_,hop⟩
    intro hab
    simp [hi,hab] at hcard
  · simp [hi] at hlen

def nextF (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool) (g : Gate)
    (j : ℕ) (x : Fin n → Bool) : Bool :=
  if j = L.length then g.op.eval (g.inputs.map fun a => F a x) else F j x

theorem tight_step (t : ℕ) (L : List (Finset (Fin n))) (F : ℕ → (Fin n → Bool) → Bool)
    (g : Gate) (ho : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (hc : Cnt t L) (ht : Tight t L F) :
    Tight (t+1) (L ++ [gateSupp L g]) (nextF L F g) := by
  intro W heq
  have hW : L.length ∈ W := by
    by_contra hn
    have hU : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
        (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun h => hn (h ▸ hj))
    rw [hU] at heq
    have := hc W
    omega
  let E := W.erase L.length
  let B := (reads g).toFinset
  let P := E ∪ B
  have hEc : E.card+1 = W.card := Finset.card_erase_add_one hW
  have hBc : B.card ≤ 2 := le_trans (List.toFinset_card_le _) (le_trans (reads_le g) hlen)
  have hPc : P.card ≤ E.card + B.card := Finset.card_union_le _ _
  have hU : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅) =
      (P.biUnion fun j => L.getD j ∅) := union_step L g W hW
  rw [hU] at heq
  have hcP := hc P
  have hB2 : B.card = 2 := by omega
  have hPexact : P.card = E.card + B.card := by omega
  have hTexact : (P.biUnion fun j => L.getD j ∅).card = t + P.card := by omega
  have hEB : Disjoint E B := Finset.card_union_eq_card_add_card.mp hPexact
  obtain ⟨a,b,hin,hab,hop⟩ := binary_of_reads g ho hlen hB2
  have hreads : reads g = [a,b] := by rcases hop with h | h <;> simp [reads,h,hin]
  have haB : a ∈ B := by simp [B,hreads]
  have hbB : b ∈ B := by simp [B,hreads]
  have haP : a ∈ P := Finset.mem_union_right _ haB
  have hbP : b ∈ P := Finset.mem_union_right _ hbB
  have hF := ht P hTexact
  have hEP : E ⊆ P := Finset.subset_union_left
  have hneA : ∀ w ∈ E, w ≠ a := by
    intro w hw hwa; subst w
    exact Finset.disjoint_left.mp hEB hw haB
  have hneB : ∀ w ∈ E, w ≠ b := by
    intro w hw hwb; subst w
    exact Finset.disjoint_left.mp hEB hw hbB
  have hS : gateSupp L g = L.getD a ∅ ∪ L.getD b ∅ := by simp [gateSupp,hreads]
  have hnew : RO (gateSupp L g) (nextF L F g L.length) := by
    rw [hS]
    have hd := hF.2 a haP b hbP hab
    rcases hop with hop | hop
    · have hf : nextF L F g L.length = (fun x => F a x && F b x) := by
        funext x; simp [nextF,hin,hop,GateOp.eval]
      rw [hf]; exact ro_and hd (hF.1 a haP) (hF.1 b hbP)
    · have hf : nextF L F g L.length = (fun x => F a x || F b x) := by
        funext x; simp [nextF,hin,hop,GateOp.eval]
      rw [hf]; exact ro_or hd (hF.1 a haP) (hF.1 b hbP)
  have hother : ∀ w ∈ E, (L ++ [gateSupp L g]).getD w ∅ = L.getD w ∅ :=
    fun w hw => getD_snoc_ne _ _ _ _ (Finset.ne_of_mem_erase hw)
  have hnewdis : ∀ w ∈ E, Disjoint (gateSupp L g) (L.getD w ∅) := by
    intro w hw
    rw [hS,Finset.disjoint_union_left]
    exact ⟨hF.2 a haP w (hEP hw) (hneA w hw).symm,
      hF.2 b hbP w (hEP hw) (hneB w hw).symm⟩
  constructor
  · intro w hw
    by_cases hwk : w = L.length
    · subst w
      rw [getD_snoc_eq]
      exact hnew
    · have hwE : w ∈ E := Finset.mem_erase.mpr ⟨hwk,hw⟩
      rw [hother w hwE]
      have hf : nextF L F g w = F w := by funext x; simp [nextF,hwk]
      rw [hf]
      exact hF.1 w (hEP hwE)
  · intro w hw v hv hne
    by_cases hwk : w = L.length
    · subst w
      have hvE : v ∈ E := Finset.mem_erase.mpr ⟨hne.symm,hv⟩
      rw [getD_snoc_eq,hother v hvE]
      exact hnewdis v hvE
    · have hwE : w ∈ E := Finset.mem_erase.mpr ⟨hwk,hw⟩
      rw [hother w hwE]
      by_cases hvk : v = L.length
      · subst v
        rw [getD_snoc_eq]
        exact (hnewdis w hwE).symm
      · have hvE : v ∈ E := Finset.mem_erase.mpr ⟨hvk,hv⟩
        rw [hother v hvE]
        exact hF.2 w (hEP hwE) v (hEP hvE) hne

theorem tight_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n)))
    (v : (Fin n → Bool) → List Bool), (∀ x, (v x).length = L.length) →
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
    Cnt t L → Tight t L (fun j x => (v x).getD j false) →
    Tight (t+gs.length) (suppsFrom gs L) (fun j x => (wiresFrom gs (v x)).getD j false) := by
  induction gs with
  | nil => intro t L v hv _ hc ht; exact ht
  | cons g gs ih =>
    intro t L v hv hg hc ht
    let v' := fun x : Fin n → Bool => v x ++ [g.op.eval (g.inputs.map fun a => (v x).getD a false)]
    have hv' : ∀ x, (v' x).length = (L ++ [gateSupp L g]).length := by
      intro x; simp [v',hv x]
    have hf : (fun j x => (v' x).getD j false) =
        nextF L (fun j x => (v x).getD j false) g := by
      funext j x
      by_cases hj : j = L.length
      · subst j
        simp only [nextF,ite_true]
        dsimp only [v']
        rw [← hv x,getD_snoc_eq]
      · simp only [nextF,hj,ite_false]
        exact getD_snoc_ne _ _ _ _ (by rw [hv x]; exact hj)
    have hgg := hg g List.mem_cons_self
    have ht' : Tight (t+1) (L ++ [gateSupp L g]) (fun j x => (v' x).getD j false) := by
      rw [hf]
      exact tight_step t L _ g hgg.1 hgg.2 hc ht
    have hres := ih (t+1) (L ++ [gateSupp L g]) v' hv'
      (fun g' h => hg g' (List.mem_cons_of_mem g h)) (cnt_step t L g hgg.2 hc) ht'
    simpa only [List.length_cons,show t+(gs.length+1)=t+1+gs.length by omega,
      suppsFrom,wiresFrom,List.foldl_cons,v'] using hres

theorem wire_read_once (C : Circuit) (n k w : Nat)
    (hk : k ≤ C.gates.length) (hw : w < n+k)
    (hfan : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (E : Finset (Fin n)) (hE : E.card = k+1)
    (hsens : ∀ i ∈ E, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧
      (C.wires (List.ofFn x)).getD w false ≠ (C.wires (List.ofFn y)).getD w false) :
    RO E (fun x => (C.wires (List.ofFn x)).getD w false) := by
  let gs := C.gates.take k
  let L := suppsFrom gs (inputSupps n)
  let S := L.getD w ∅
  have hlen : gs.length = k := by simp [gs,List.length_take,Nat.min_eq_left hk]
  have hfan' : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hfan g (List.mem_of_mem_take hg)
  have hc := cnt_suppsFrom gs 0 (inputSupps n) (fun g hg => (hfan' g hg).2) cnt_inputs
  have hSc : S.card ≤ k+1 := by
    have := hc {w}
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using this
  have hdep : ∀ x y : Fin n → Bool, (∀ i ∈ S,x i=y i) →
      (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
    intro x y hxy
    rw [getD_take_eq C n k w hk hw x,getD_take_eq C n k w hk hw y]
    exact (agree_wiresFrom x y gs _ _ _ (agree_inputs x y)).2.2 w hxy
  have hsub : E ⊆ S := by
    intro i hi
    by_contra hni
    obtain ⟨x,y,hxy,hne⟩ := hsens i hi
    apply hne (hdep x y ?_)
    intro j hj
    exact hxy j (fun h => hni (h ▸ hj))
  have hES : E = S := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hT := tight_suppsFrom gs 0 (inputSupps n) (fun x => List.ofFn x)
    (fun x => by simp [inputSupps]) hfan' cnt_inputs tight_inputs
  have heq : (({w} : Finset ℕ).biUnion fun j => L.getD j ∅).card = (0+gs.length)+({w} : Finset ℕ).card := by
    have hS : S.card = k+1 := by rw [←hES]; exact hE
    simpa only [Finset.singleton_biUnion,Finset.card_singleton,zero_add,hlen] using hS
  have hR := (hT {w} heq).1 w (Finset.mem_singleton_self w)
  change RO S _ at hR
  rw [←hES] at hR
  have hf : (fun x : Fin n → Bool => (wiresFrom gs (List.ofFn x)).getD w false) =
      (fun x => (C.wires (List.ofFn x)).getD w false) := by
    funext x; exact (getD_take_eq C n k w hk hw x).symm
  change RO E (fun x : Fin n → Bool => (wiresFrom gs (List.ofFn x)).getD w false) at hR
  rw [hf] at hR
  exact hR

end PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce

namespace PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath
open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce

variable {n : ℕ} {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}

theorem ro_nonempty (h : RO S f) : S.Nonempty := by
  apply h (fun S _ => S.Nonempty)
  · intro i; exact Finset.singleton_nonempty i
  · intro A B a b hd ha hb
    exact ⟨ha.mono Finset.subset_union_left,ha.mono Finset.subset_union_left⟩

theorem ro_zero (h : RO S f) (x : Fin n → Bool) (hx : ∀ i ∈ S,x i=false) : f x=false := by
  apply h (fun S f => ∀ x, (∀ i ∈ S,x i=false) → f x=false) ?_ ?_ x hx
  · intro i x hx; exact hx i (Finset.mem_singleton_self _)
  · intro A B a b hd ha hb
    constructor <;> intro x hx
    · dsimp only
      rw [ha x (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb x (fun i hi => hx i (Finset.mem_union_right _ hi))]; rfl
    · dsimp only
      rw [ha x (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb x (fun i hi => hx i (Finset.mem_union_right _ hi))]; rfl

theorem ro_depends (h : RO S f) (x y : Fin n → Bool) (hx : ∀ i ∈ S,x i=y i) : f x=f y := by
  apply h (fun S f => ∀ x y, (∀ i ∈ S,x i=y i) → f x=f y) ?_ ?_ x y hx
  · intro i x y hx; exact hx i (Finset.mem_singleton_self _)
  · intro A B a b hd ha hb
    constructor <;> intro x y hx <;> dsimp only <;>
      rw [ha x y (fun i hi => hx i (Finset.mem_union_left _ hi)),
        hb x y (fun i hi => hx i (Finset.mem_union_right _ hi))]

theorem ro_mono (h : RO S f) (x y : Fin n → Bool)
    (hxy : ∀ i,x i=true → y i=true) (hf : f x=true) : f y=true := by
  apply h (fun _ f => ∀ x y, (∀ i,x i=true → y i=true) → f x=true → f y=true) ?_ ?_ x y hxy hf
  · intro i x y hxy hf; exact hxy i hf
  · intro A B a b hd ha hb
    constructor
    · intro x y hxy hf
      simp only [Bool.and_eq_true] at hf ⊢
      exact ⟨ha x y hxy hf.1,hb x y hxy hf.2⟩
    · intro x y hxy hf
      simp only [Bool.or_eq_true] at hf ⊢
      exact hf.elim (fun h => Or.inl (ha x y hxy h)) (fun h => Or.inr (hb x y hxy h))

theorem ro_split (h : RO S f) :
    (∃ i : Fin n,S={i} ∧ f=(fun x => x i)) ∨
    ∃ A B a b, Disjoint A B ∧ S=A∪B ∧ RO A a ∧ RO B b ∧
      (f=(fun x => a x && b x) ∨ f=(fun x => a x || b x)) := by
  let Q := fun S f => RO S f ∧
    ((∃ i : Fin n,S={i} ∧ f=(fun x => x i)) ∨
    ∃ A B a b, Disjoint A B ∧ S=A∪B ∧ RO A a ∧ RO B b ∧
      (f=(fun x => a x && b x) ∨ f=(fun x => a x || b x)))
  have hQ : Q S f := h Q (fun i => ⟨ro_leaf i,Or.inl ⟨i,rfl,rfl⟩⟩) (by
    intro A B a b hd ha hb
    constructor
    · exact ⟨ro_and hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inl rfl⟩⟩
    · exact ⟨ro_or hd ha.1 hb.1,Or.inr ⟨A,B,a,b,hd,rfl,ha.1,hb.1,Or.inr rfl⟩⟩)
  exact hQ.2

def pair (i j : Fin n) : Fin n → Bool := fun k => decide (k=i ∨ k=j)
def single (i : Fin n) : Fin n → Bool := fun k => decide (k=i)

theorem pair_comm (i j : Fin n) : pair i j=pair j i := by funext k; simp [pair,or_comm]

theorem pair_zero (h : RO S f) (i j : Fin n) (hi : i ∉ S) (hj : j ∉ S) : f (pair i j)=false := by
  apply ro_zero h
  intro k hk
  simp only [pair,decide_eq_false_iff_not,not_or]
  exact ⟨fun hki => hi (hki ▸ hk),fun hkj => hj (hkj ▸ hk)⟩

theorem pair_left (h : RO S f) (i j : Fin n) (hj : j ∉ S) :
    f (pair i j)=f (single i) := by
  apply ro_depends h
  intro k hk
  have hkj : k≠j := fun hkj => hj (hkj ▸ hk)
  simp [pair,single,hkj]

theorem pair_right (h : RO S f) (i j : Fin n) (hi : i ∉ S) :
    f (pair i j)=f (single j) := by rw [pair_comm]; exact pair_left h j i hi

end PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath

namespace PEqualNP.Outside.L_meta_32063.L853.R017

open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath

variable {n : ℕ}

def NoSingle (f : (Fin n → Bool) → Bool) : Prop := ∀ i, f (single i) = false

def PairCover (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i ∈ S, ∃ j ∈ S, f (pair i j) = true

def Quadratic (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true ↔ ∃ i ∈ S, ∃ j ∈ S, f (pair i j) = true ∧ x i = true ∧ x j = true

theorem single_le {i : Fin n} {x : Fin n → Bool} (hi : x i = true) :
    ∀ j, single i j = true → x j = true := by
  intro j hj
  have : j = i := by simpa [single] using hj
  simpa [this] using hi

theorem pair_le {i j : Fin n} {x : Fin n → Bool} (hi : x i = true) (hj : x j = true) :
    ∀ t, pair i j t = true → x t = true := by
  intro t ht
  have : t = i ∨ t = j := by simpa [pair] using ht
  rcases this with rfl | rfl <;> assumption

theorem ro_some_true {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (x : Fin n → Bool) (hx : f x = true) : ∃ i ∈ S, x i = true := by
  by_contra hn
  have hz : ∀ i ∈ S, x i = false := by
    intro i hi
    have h : x i ≠ true := fun ht => hn ⟨i, hi, ht⟩
    exact Bool.eq_false_iff.mpr h
  have h := ro_zero hf x hz
  rw [hx] at h
  contradiction

theorem ro_all_singletons {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hs : ∀ i ∈ S, f (single i) = true) (x : Fin n → Bool) :
    f x = true ↔ ∃ i ∈ S, x i = true := by
  constructor
  · exact ro_some_true hf x
  · rintro ⟨i, hi, hx⟩
    exact ro_mono hf _ _ (single_le hx) (hs i hi)

theorem and_cover_singletons {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hc : PairCover (A ∪ B) (fun x => a x && b x)) :
    (∀ i ∈ A, a (single i) = true) ∧ (∀ j ∈ B, b (single j) = true) := by
  constructor
  · intro i hi
    obtain ⟨j, hj, hp⟩ := hc i (Finset.mem_union_left _ hi)
    have hia : i ∉ B := Finset.disjoint_left.mp hd hi
    have hja : j ∉ A := by
      intro hjA
      have hjB : j ∉ B := Finset.disjoint_left.mp hd hjA
      have hz := pair_zero hb i j hia hjB
      simp only [hz, Bool.and_false] at hp
      contradiction
    have hpA : a (pair i j) = true := (by simpa only [Bool.and_eq_true] using hp : a (pair i j) = true ∧ b (pair i j) = true).1
    rwa [pair_left ha i j hja] at hpA
  · intro i hi
    obtain ⟨j, hj, hp⟩ := hc i (Finset.mem_union_right _ hi)
    have hia : i ∉ A := Finset.disjoint_right.mp hd hi
    have hja : j ∉ B := by
      intro hjB
      have hjA : j ∉ A := Finset.disjoint_right.mp hd hjB
      have hz := pair_zero ha i j hia hjA
      simp only [hz, Bool.false_and] at hp
      contradiction
    have hpB : b (pair i j) = true := (by simpa only [Bool.and_eq_true] using hp : a (pair i j) = true ∧ b (pair i j) = true).2
    rwa [pair_left hb i j hja] at hpB

theorem or_cover_left {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hs : NoSingle (fun x => a x || b x))
    (hc : PairCover (A ∪ B) (fun x => a x || b x)) : PairCover A a := by
  intro i hi
  obtain ⟨j, hj, hp⟩ := hc i (Finset.mem_union_left _ hi)
  have hia : i ∉ B := Finset.disjoint_left.mp hd hi
  have hsA : ∀ t, a (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).1
  have hsB : ∀ t, b (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).2
  have hpA : a (pair i j) = true := by
    have hp' : a (pair i j) = true ∨ b (pair i j) = true := by simpa only [Bool.or_eq_true] using hp
    rcases hp' with h | h
    · exact h
    · rw [pair_right hb i j hia, hsB j] at h
      contradiction
  have hjA : j ∈ A := by
    by_contra hjA
    rw [pair_left ha i j hjA, hsA i] at hpA
    contradiction
  exact ⟨j, hjA, hpA⟩

theorem pair_cover_quadratic {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hs : NoSingle f) (hc : PairCover S f) : Quadratic S f := by
  let Q := fun (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) => RO S f ∧ (NoSingle f → PairCover S f → Quadratic S f)
  have hQ : Q S f := hf Q (by
    intro i
    refine ⟨ro_leaf i, ?_⟩
    intro hs hc
    have h := hs i
    simp [single] at h) (by
    intro A B a b hd ha hb
    constructor
    · refine ⟨ro_and hd ha.1 hb.1, ?_⟩
      intro hs hc x
      constructor
      · intro hx
        obtain ⟨hi, hj⟩ := and_cover_singletons hd ha.1 hb.1 hc
        obtain ⟨i, hiA, hxi⟩ := ro_some_true ha.1 x (by simpa only [Bool.and_eq_true] using hx : a x = true ∧ b x = true).1
        obtain ⟨j, hjB, hxj⟩ := ro_some_true hb.1 x (by simpa only [Bool.and_eq_true] using hx : a x = true ∧ b x = true).2
        refine ⟨i, Finset.mem_union_left _ hiA, j, Finset.mem_union_right _ hjB, ?_, hxi, hxj⟩
        have hjA : j ∉ A := Finset.disjoint_right.mp hd hjB
        have hiB : i ∉ B := Finset.disjoint_left.mp hd hiA
        dsimp only
        rw [pair_left ha.1 i j hjA, pair_right hb.1 i j hiB, hi i hiA, hj j hjB]
        rfl
      · rintro ⟨i, hi, j, hj, hp, hxi, hxj⟩
        exact ro_mono (ro_and hd ha.1 hb.1) _ _ (pair_le hxi hxj) hp
    · refine ⟨ro_or hd ha.1 hb.1, ?_⟩
      intro hs hc x
      have hsA : NoSingle a := fun t => (Bool.or_eq_false_iff.mp (hs t)).1
      have hsB : NoSingle b := fun t => (Bool.or_eq_false_iff.mp (hs t)).2
      have hcA := or_cover_left hd ha.1 hb.1 hs hc
      have hcB : PairCover B b := by
        have hs' : NoSingle (fun x => b x || a x) := by simpa only [Bool.or_comm] using hs
        have hc' : PairCover (B ∪ A) (fun x => b x || a x) := by
          simpa only [Finset.union_comm, Bool.or_comm] using hc
        exact or_cover_left hd.symm hb.1 ha.1 hs' hc'
      constructor
      · intro hx
        have hx' : a x = true ∨ b x = true := by simpa only [Bool.or_eq_true] using hx
        rcases hx' with h | h
        · obtain ⟨i, hi, j, hj, hp, hxi, hxj⟩ := (ha.2 hsA hcA x).mp h
          refine ⟨i, Finset.mem_union_left _ hi, j, Finset.mem_union_left _ hj, ?_, hxi, hxj⟩
          simp only [hp, Bool.true_or]
        · obtain ⟨i, hi, j, hj, hp, hxi, hxj⟩ := (hb.2 hsB hcB x).mp h
          refine ⟨i, Finset.mem_union_right _ hi, j, Finset.mem_union_right _ hj, ?_, hxi, hxj⟩
          simp only [hp, Bool.or_true]
      · rintro ⟨i, hi, j, hj, hp, hxi, hxj⟩
        exact ro_mono (ro_or hd ha.1 hb.1) _ _ (pair_le hxi hxj) hp)
  exact hQ.2 hs hc

end PEqualNP.Outside.L_meta_32063.L853.R017

namespace PEqualNP.Outside.L_meta_32063.L853.R017

open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath

variable {n : ℕ}

theorem or_pair_inside_left {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hs : NoSingle (fun x => a x || b x))
    {i j : Fin n} (hi : i ∈ A) (hp : (a (pair i j) || b (pair i j)) = true) :
    j ∈ A ∧ a (pair i j) = true := by
  have hiB : i ∉ B := Finset.disjoint_left.mp hd hi
  have hsA : ∀ t, a (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).1
  have hsB : ∀ t, b (single t) = false := fun t => (Bool.or_eq_false_iff.mp (hs t)).2
  have hpA : a (pair i j) = true := by
    rcases Bool.or_eq_true_iff.mp hp with h | h
    · exact h
    · rw [pair_right hb i j hiB, hsB j] at h
      contradiction
  refine ⟨?_, hpA⟩
  by_contra hjA
  rw [pair_left ha i j hjA, hsA i] at hpA
  contradiction

theorem and_cross_pair {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hc : PairCover (A ∪ B) (fun x => a x && b x))
    {i j : Fin n} (hi : i ∈ A) (hj : j ∈ B) :
    (a (pair i j) && b (pair i j)) = true := by
  obtain ⟨hsA, hsB⟩ := and_cover_singletons hd ha hb hc
  have hiB : i ∉ B := Finset.disjoint_left.mp hd hi
  have hjA : j ∉ A := Finset.disjoint_right.mp hd hj
  rw [pair_left ha i j hjA, pair_right hb i j hiB, hsA i hi, hsB j hj]
  rfl

theorem and_pair_cross_left {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (hb : RO B b)
    {i j : Fin n} (hi : i ∈ A) (hp : (a (pair i j) && b (pair i j)) = true) :
    j ∈ B := by
  by_contra hjB
  have hiB : i ∉ B := Finset.disjoint_left.mp hd hi
  rw [pair_zero hb i j hiB hjB, Bool.and_false] at hp
  contradiction

def Matched (mate : Fin n → Fin n) (color : Fin n → Bool)
    (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  NoSingle f ∧
  (∀ i ∈ S, mate i ∈ S) ∧
  (∀ i ∈ S, f (pair i (mate i)) = true) ∧
  (∀ i j, color i ≠ color j → j ≠ mate i → f (pair i j) = false)

theorem matched_cover {mate : Fin n → Fin n} {color : Fin n → Bool}
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool} (h : Matched mate color S f) :
    PairCover S f := fun i hi => ⟨mate i, h.2.1 i hi, h.2.2.1 i hi⟩

theorem matched_or_left {mate : Fin n → Fin n} {color : Fin n → Bool}
    {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hm : Matched mate color (A ∪ B) (fun x => a x || b x)) :
    Matched mate color A a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (Bool.or_eq_false_iff.mp (hm.1 i)).1
  · intro i hi
    exact (or_pair_inside_left hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).1
  · intro i hi
    exact (or_pair_inside_left hd ha hb hm.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))).2
  · intro i j hc hj
    exact (Bool.or_eq_false_iff.mp (hm.2.2.2 i j hc hj)).1

theorem matched_or_right {mate : Fin n → Fin n} {color : Fin n → Bool}
    {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hm : Matched mate color (A ∪ B) (fun x => a x || b x)) :
    Matched mate color B b := by
  have h : Matched mate color (B ∪ A) (fun x => b x || a x) := by
    simpa only [Finset.union_comm, Bool.or_comm] using hm
  exact matched_or_left hd.symm hb ha h

theorem and_color_injective_left {mate : Fin n → Fin n} {color : Fin n → Bool}
    (hmi : Function.Involutive mate) (hcol : ∀ i, color (mate i) ≠ color i)
    {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : RO A a) (hb : RO B b)
    (hm : Matched mate color (A ∪ B) (fun x => a x && b x)) :
    ∀ i ∈ A, ∀ j ∈ A, color i = color j → i = j := by
  intro i hi j hj hij
  have hmj : mate j ∈ B := and_pair_cross_left hd hb hj
    (hm.2.2.1 j (Finset.mem_union_left _ hj))
  have ht : (a (pair i (mate j)) && b (pair i (mate j))) = true :=
    and_cross_pair hd ha hb (matched_cover hm) hi hmj
  have hcm : color i ≠ color (mate j) := by
    intro h
    exact hcol j (h.symm.trans hij)
  have hmate : mate j = mate i := by
    by_contra hne
    have hf := hm.2.2.2 i (mate j) hcm hne
    dsimp only at hf
    rw [hf] at ht
    contradiction
  exact (hmi.injective hmate).symm

def SameColorMatching (color : Fin n → Bool) (S : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ l ∈ S, color i = color j → color i = color l →
    f (pair i j) = true → f (pair i l) = true → j = l

theorem matched_same_color_matching {mate : Fin n → Fin n} {color : Fin n → Bool}
    (hmi : Function.Involutive mate) (hcol : ∀ i, color (mate i) ≠ color i)
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hm : Matched mate color S f) : SameColorMatching color S f := by
  let Q := fun (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) =>
    RO S f ∧ (Matched mate color S f → SameColorMatching color S f)
  have hQ : Q S f := hf Q (by
    intro i
    refine ⟨ro_leaf i, ?_⟩
    intro hm
    have hs := hm.1 i
    simp [single] at hs) (by
    intro A B a b hd ha hb
    constructor
    · refine ⟨ro_and hd ha.1 hb.1, ?_⟩
      intro hm i hi j hj l hl hij hil hpj hpl
      have hinjA := and_color_injective_left hmi hcol hd ha.1 hb.1 hm
      have hm' : Matched mate color (B ∪ A) (fun x => b x && a x) := by
        simpa only [Finset.union_comm, Bool.and_comm] using hm
      have hinjB := and_color_injective_left hmi hcol hd.symm hb.1 ha.1 hm'
      rcases Finset.mem_union.mp hi with hi | hi
      · have hjB := and_pair_cross_left hd hb.1 hi hpj
        have hlB := and_pair_cross_left hd hb.1 hi hpl
        exact hinjB j hjB l hlB (hij.symm.trans hil)
      · have hpj' : (b (pair i j) && a (pair i j)) = true := by simpa only [Bool.and_comm] using hpj
        have hpl' : (b (pair i l) && a (pair i l)) = true := by simpa only [Bool.and_comm] using hpl
        have hjA := and_pair_cross_left hd.symm ha.1 hi hpj'
        have hlA := and_pair_cross_left hd.symm ha.1 hi hpl'
        exact hinjA j hjA l hlA (hij.symm.trans hil)
    · refine ⟨ro_or hd ha.1 hb.1, ?_⟩
      intro hm i hi j hj l hl hij hil hpj hpl
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨hjA, hpjA⟩ := or_pair_inside_left hd ha.1 hb.1 hm.1 hi hpj
        obtain ⟨hlA, hplA⟩ := or_pair_inside_left hd ha.1 hb.1 hm.1 hi hpl
        exact ha.2 (matched_or_left hd ha.1 hb.1 hm) i hi j hjA l hlA hij hil hpjA hplA
      · have hm' : Matched mate color (B ∪ A) (fun x => b x || a x) := by
          simpa only [Finset.union_comm, Bool.or_comm] using hm
        have hpj' : (b (pair i j) || a (pair i j)) = true := by simpa only [Bool.or_comm] using hpj
        have hpl' : (b (pair i l) || a (pair i l)) = true := by simpa only [Bool.or_comm] using hpl
        obtain ⟨hjB, hpjB⟩ := or_pair_inside_left hd.symm hb.1 ha.1 hm'.1 hi hpj'
        obtain ⟨hlB, hplB⟩ := or_pair_inside_left hd.symm hb.1 ha.1 hm'.1 hi hpl'
        exact hb.2 (matched_or_right hd ha.1 hb.1 hm) i hi j hjB l hlB hij hil hpjB hplB)
  exact hQ.2 hm

end PEqualNP.Outside.L_meta_32063.L853.R017

namespace PEqualNP.Outside.L_meta_32063.L853.R017
open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath
variable {n : ℕ}

theorem matched_mirror_true {mate : Fin n → Fin n} {color : Fin n → Bool}
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hm : Matched mate color S f) :
    ∀ i ∈ S, ∀ j ∈ S, f (pair i j) = true → f (pair (mate i) (mate j)) = true := by
  let Q := fun (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) =>
    RO S f ∧ (Matched mate color S f →
      ∀ i ∈ S, ∀ j ∈ S, f (pair i j) = true → f (pair (mate i) (mate j)) = true)
  have hQ : Q S f := hf Q (by
    intro i
    refine ⟨ro_leaf i, ?_⟩
    intro hm
    have hs := hm.1 i
    simp [single] at hs) (by
    intro A B a b hd ha hb
    constructor
    · refine ⟨ro_and hd ha.1 hb.1, ?_⟩
      intro hm i hi j hj hp
      have hm' : Matched mate color (B ∪ A) (fun x => b x && a x) := by
        simpa only [Finset.union_comm, Bool.and_comm] using hm
      rcases Finset.mem_union.mp hi with hi | hi
      · have hjB := and_pair_cross_left hd hb.1 hi hp
        have hmiB := and_pair_cross_left hd hb.1 hi (hm.2.2.1 i (Finset.mem_union_left _ hi))
        have hmjA := and_pair_cross_left hd.symm ha.1 hjB
          (hm'.2.2.1 j (Finset.mem_union_left _ hjB))
        have h := and_cross_pair hd.symm hb.1 ha.1 (matched_cover hm') hmiB hmjA
        simpa only [Bool.and_comm] using h
      · have hp' : (b (pair i j) && a (pair i j)) = true := by
          simpa only [Bool.and_comm] using hp
        have hjA := and_pair_cross_left hd.symm ha.1 hi hp'
        have hmiA := and_pair_cross_left hd.symm ha.1 hi
          (hm'.2.2.1 i (Finset.mem_union_left _ hi))
        have hmjB := and_pair_cross_left hd hb.1 hjA (hm.2.2.1 j (Finset.mem_union_left _ hjA))
        exact and_cross_pair hd ha.1 hb.1 (matched_cover hm) hmiA hmjB
    · refine ⟨ro_or hd ha.1 hb.1, ?_⟩
      intro hm i hi j hj hp
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨hjA, hpA⟩ := or_pair_inside_left hd ha.1 hb.1 hm.1 hi hp
        have h := ha.2 (matched_or_left hd ha.1 hb.1 hm) i hi j hjA hpA
        dsimp only
        rw [h, Bool.true_or]
      · have hm' : Matched mate color (B ∪ A) (fun x => b x || a x) := by
          simpa only [Finset.union_comm, Bool.or_comm] using hm
        have hp' : (b (pair i j) || a (pair i j)) = true := by
          simpa only [Bool.or_comm] using hp
        obtain ⟨hjB, hpB⟩ := or_pair_inside_left hd.symm hb.1 ha.1 hm'.1 hi hp'
        have h := hb.2 (matched_or_right hd ha.1 hb.1 hm) i hi j hjB hpB
        dsimp only
        rw [h, Bool.or_true])
  exact hQ.2 hm

theorem matched_mirror {mate : Fin n → Fin n} {color : Fin n → Bool}
    (hmi : Function.Involutive mate)
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hm : Matched mate color S f)
    {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S) :
    f (pair i j) = f (pair (mate i) (mate j)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact matched_mirror_true hf hm i hi j hj
  · intro h
    have h' := matched_mirror_true hf hm (mate i) (hm.2.1 i hi) (mate j) (hm.2.1 j hj) h
    simpa only [hmi i, hmi j] using h'

end PEqualNP.Outside.L_meta_32063.L853.R017

namespace PEqualNP.Outside.L_meta_32063.L853.R017

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

theorem relation_involution_commutes {R : α → α → Prop} {p : Equiv.Perm α}
    (hp : ∀ a b, R a b ↔ p a = b ∧ b ≠ a)
    (σ : α → α) (hσ : Function.Involutive σ)
    (hR : ∀ a b, R a b → R (σ a) (σ b)) :
    ∀ a, p (σ a) = σ (p a) := by
  intro a
  by_cases he : p a = a
  · by_cases he' : p (σ a) = σ a
    · rw [he, he']
    · have h := hR (σ a) (p (σ a)) ((hp _ _).2 ⟨rfl, he'⟩)
      rw [hσ a] at h
      obtain ⟨hpa, hne⟩ := (hp _ _).1 h
      exact False.elim (hne (hpa.symm.trans he))
  · have h := hR a (p a) ((hp _ _).2 ⟨rfl, he⟩)
    exact ((hp _ _).1 h).1

end PEqualNP.Outside.L_meta_32063.L853.R017

namespace PEqualNP.Outside.L_meta_32063.L853.R017
open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath
variable {n : ℕ}

theorem bool_opposite_equal : ∀ a b c d : Bool, a ≠ c → b ≠ d → c = d → a = b := by decide

theorem matched_involution_normal_form {mate : Fin n → Fin n} {color : Fin n → Bool}
    (hmi : Function.Involutive mate) (hcol : ∀ i, color (mate i) ≠ color i)
    {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (hf : RO S f) (hm : Matched mate color S f) :
    ∃ p : Equiv.Perm (Fin n), Function.Involutive p ∧
      (∀ i, color (p i) = color i) ∧
      (∀ i, p (mate i) = mate (p i)) ∧
      (∀ i, i ∉ S → p i = i) ∧
      (∀ x, f x = true ↔ ∃ i ∈ S,
        (x i = true ∧ x (mate i) = true) ∨
        (p i ≠ i ∧ x i = true ∧ x (p i) = true)) ∧
      (∀ i j, (i ∈ S ∧ j ∈ S ∧ color i = color j ∧ f (pair i j) = true) ↔
        p i = j ∧ j ≠ i) := by
  classical
  let R : Fin n → Fin n → Prop := fun i j =>
    i ∈ S ∧ j ∈ S ∧ color i = color j ∧ f (pair i j) = true
  have hsym : ∀ {i j}, R i j → R j i := by
    intro i j h
    refine ⟨h.2.1, h.1, h.2.2.1.symm, ?_⟩
    rw [pair_comm]
    exact h.2.2.2
  have hirr : ∀ i, ¬ R i i := by
    intro i h
    have hp : pair i i = single i := by funext j; simp [pair, single]
    have htrue := h.2.2.2
    rw [hp, hm.1 i] at htrue
    contradiction
  have hunique : ∀ i j l, R i j → R i l → j = l := by
    intro i j l h1 h2
    exact matched_same_color_matching hmi hcol hf hm i h1.1 j h1.2.1 l h2.2.1
      h1.2.2.1 h2.2.2.1 h1.2.2.2 h2.2.2.2
  obtain ⟨p, hpi, hp, hpu⟩ := relation_involution R hsym hirr hunique
  have hcolor : ∀ i, color (p i) = color i := by
    intro i
    by_cases he : p i = i
    · rw [he]
    · exact ((hp i (p i)).2 ⟨rfl, he⟩).2.2.1.symm
  have hmirror : ∀ i j, R i j → R (mate i) (mate j) := by
    intro i j h
    refine ⟨hm.2.1 i h.1, hm.2.1 j h.2.1, ?_, ?_⟩
    · exact bool_opposite_equal _ _ _ _ (hcol i) (hcol j) h.2.2.1
    · exact matched_mirror_true hf hm i h.1 j h.2.1 h.2.2.2
  have hcomm := relation_involution_commutes hp mate hmi hmirror
  have hout : ∀ i, i ∉ S → p i = i := by
    intro i hi
    by_contra he
    exact hi ((hp i (p i)).2 ⟨rfl, he⟩).1
  refine ⟨p, hpi, hcolor, hcomm, hout, ?_, hp⟩
  intro x
  constructor
  · intro hfx
    obtain ⟨i, hi, j, hj, hpair, hxi, hxj⟩ :=
      (pair_cover_quadratic hf hm.1 (matched_cover hm) x).1 hfx
    by_cases hc : color i = color j
    · have hrij : R i j := ⟨hi, hj, hc, hpair⟩
      obtain ⟨hpij, hji⟩ := (hp i j).1 hrij
      refine ⟨i, hi, Or.inr ⟨?_, hxi, ?_⟩⟩
      · simpa only [hpij] using hji
      · simpa only [hpij] using hxj
    · have hjm : j = mate i := by
        by_contra hne
        have hz := hm.2.2.2 i j hc hne
        rw [hz] at hpair
        contradiction
      exact ⟨i, hi, Or.inl ⟨hxi, hjm ▸ hxj⟩⟩
  · rintro ⟨i, hi, h | h⟩
    · exact ro_mono hf _ _ (pair_le h.1 h.2) (hm.2.2.1 i hi)
    · have hr := (hp i (p i)).2 ⟨rfl, h.1⟩
      exact ro_mono hf _ _ (pair_le h.2.1 h.2.2) hr.2.2.2

end PEqualNP.Outside.L_meta_32063.L853.R017

namespace PEqualNP.Outside.L_meta_32063.L853.R017.RowColumn
open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath
variable {k : ℕ}

abbrev row (i : Fin k) : Fin (k+k) := Fin.castAdd k i
abbrev col (i : Fin k) : Fin (k+k) := Fin.natAdd k i
def mate : Fin (k+k) → Fin (k+k) := Fin.append col row
def color : Fin (k+k) → Bool := Fin.append (fun _ => false) (fun _ => true)

@[simp] theorem mate_row (i : Fin k) : mate (row i) = col i := Fin.append_left _ _ i
@[simp] theorem mate_col (i : Fin k) : mate (col i) = row i := Fin.append_right _ _ i
@[simp] theorem color_row (i : Fin k) : color (row i) = false := Fin.append_left _ _ i
@[simp] theorem color_col (i : Fin k) : color (col i) = true := Fin.append_right _ _ i

theorem mate_involutive : Function.Involutive (mate (k := k)) := by
  intro i
  induction i using Fin.addCases with
  | left j => exact (congrArg mate (mate_row j)).trans (mate_col j)
  | right j => exact (congrArg mate (mate_col j)).trans (mate_row j)

theorem color_mate (i : Fin (k+k)) : color (mate i) ≠ color i := by
  induction i using Fin.addCases with
  | left j => change color (mate (row j)) ≠ color (row j); rw [mate_row, color_col, color_row]; decide
  | right j => change color (mate (col j)) ≠ color (col j); rw [mate_col, color_row, color_col]; decide

theorem row_injective : Function.Injective (row (k := k)) := Fin.castAdd_injective k k

theorem col_injective : Function.Injective (col (k := k)) := Fin.natAdd_injective k k

@[simp] theorem row_eq_iff (i j : Fin k) : row i = row j ↔ i = j := row_injective.eq_iff
@[simp] theorem col_eq_iff (i j : Fin k) : col i = col j ↔ i = j := col_injective.eq_iff

theorem perm_row (p : Equiv.Perm (Fin (k+k)))
    (hc : ∀ i, color (p i) = color i) (i : Fin k) : ∃ j, p (row i) = row j := by
  have hcolor := hc (row i)
  generalize he : p (row i) = v at *
  induction v using Fin.addCases with
  | left j => exact ⟨j, rfl⟩
  | right j =>
    rw [color_row] at hcolor
    change color (col j) = false at hcolor
    rw [color_col] at hcolor
    contradiction

def invFunction (p : Equiv.Perm (Fin k)) (x y : Fin k → Bool) : Bool :=
  decide (∃ i : Fin k,
    (x i = true ∧ y i = true) ∨
    (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨
      (y i = true ∧ y (p i) = true))))

theorem ro_equality_normal_form (f : (Fin (k+k) → Bool) → Bool)
    (hf : RO Finset.univ f) (hm : PEqualNP.Outside.L_meta_32063.L853.R017.Matched mate color Finset.univ f) :
    ∃ p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, f (Fin.append x y) = invFunction p x y := by
  classical
  obtain ⟨p, hpi, hcol, hcomm, hout, hfn, hedge⟩ :=
    PEqualNP.Outside.L_meta_32063.L853.R017.matched_involution_normal_form mate_involutive color_mate hf hm
  choose q hq using perm_row p hcol
  have hqi : Function.Involutive q := by
    intro i
    apply row_injective
    rw [← hq (q i), ← hq i, hpi (row i)]
  let e : Equiv.Perm (Fin k) := hqi.toPerm q
  have hp_row : ∀ i, p (row i) = row (e i) := hq
  have hp_col : ∀ i, p (col i) = col (e i) := by
    intro i
    rw [← mate_row i, hcomm, hp_row, mate_row]
  have hnrow : ∀ i, p (row i) ≠ row i ↔ e i ≠ i := by
    intro i
    rw [hp_row]
    exact not_congr (row_injective.eq_iff)
  have hncol : ∀ i, p (col i) ≠ col i ↔ e i ≠ i := by
    intro i
    rw [hp_col]
    exact not_congr (col_injective.eq_iff)
  refine ⟨e, hqi, ?_⟩
  intro x y
  apply Bool.eq_iff_iff.mpr
  rw [hfn]
  simp only [invFunction, decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv, h⟩
    induction v using Fin.addCases with
    | left i =>
      rcases h with h | ⟨hn, h1, h2⟩
      · refine ⟨i, Or.inl ?_⟩
        simpa only [mate_row, Fin.append_left, Fin.append_right] using h
      · refine ⟨i, Or.inr ⟨(hnrow i).mp hn, Or.inl ⟨?_, ?_⟩⟩⟩
        · simpa only [Fin.append_left] using h1
        · simpa only [hp_row, Fin.append_left] using h2
    | right i =>
      rcases h with h | ⟨hn, h1, h2⟩
      · refine ⟨i, Or.inl ?_⟩
        simpa only [mate_col, Fin.append_left, Fin.append_right] using h.symm
      · refine ⟨i, Or.inr ⟨(hncol i).mp hn, Or.inr ⟨?_, ?_⟩⟩⟩
        · simpa only [Fin.append_right] using h1
        · simpa only [hp_col, Fin.append_right] using h2
  · rintro ⟨i, h | ⟨hn, h | h⟩⟩
    · refine ⟨row i, Finset.mem_univ _, Or.inl ?_⟩
      simpa only [mate_row, Fin.append_left, Fin.append_right] using h
    · refine ⟨row i, Finset.mem_univ _, Or.inr ⟨(hnrow i).mpr hn, ?_, ?_⟩⟩
      · simpa only [Fin.append_left] using h.1
      · simpa only [hp_row, Fin.append_left] using h.2
    · refine ⟨col i, Finset.mem_univ _, Or.inr ⟨(hncol i).mpr hn, ?_, ?_⟩⟩
      · simpa only [Fin.append_right] using h.1
      · simpa only [hp_col, Fin.append_right] using h.2

theorem invFunction_pair_test (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (i j : Fin k) :
    invFunction p (pair i j) (fun _ => false) = true ↔ p i = j ∧ j ≠ i := by
  simp only [invFunction, decide_eq_true_eq, Bool.false_eq_true, and_false, or_false, false_or,
    pair]
  constructor
  · rintro ⟨a, hn, ha, hpa⟩
    have ha' : a = i ∨ a = j := by simpa using ha
    have hpa' : p a = i ∨ p a = j := by simpa using hpa
    rcases ha' with hai | haj
    · subst a
      rcases hpa' with h | h
      · exact False.elim (hn h)
      · exact ⟨h, fun hji => hn (h.trans hji)⟩
    · subst a
      rcases hpa' with h | h
      · have hij : p i = j := by rw [← h, hp j]
        exact ⟨hij, fun hji => hn (h.trans hji.symm)⟩
      · exact False.elim (hn h)
  · rintro ⟨hij, hji⟩
    refine ⟨i, ?_, ?_, ?_⟩
    · exact fun h => hji (hij.symm.trans h)
    · simp
    · simp [hij]

theorem invFunction_injective (p q : Equiv.Perm (Fin k))
    (hp : Function.Involutive p) (hq : Function.Involutive q)
    (he : ∀ x y, invFunction p x y = invFunction q x y) : p = q := by
  have hr : ∀ i j, (p i = j ∧ j ≠ i) ↔ (q i = j ∧ j ≠ i) := by
    intro i j
    rw [← invFunction_pair_test p hp i j, ← invFunction_pair_test q hq i j, he]
  apply Equiv.ext
  intro i
  by_cases hn : p i = i
  · by_cases hnq : q i = i
    · exact hn.trans hnq.symm
    · have h := (hr i (q i)).2 ⟨rfl, hnq⟩
      exact False.elim (hnq (h.1.symm.trans hn))
  · exact ((hr i (p i)).1 ⟨rfl, hn⟩).1.symm

theorem ro_equality_unique_normal_form (f : (Fin (k+k) → Bool) → Bool)
    (hf : RO Finset.univ f) (hm : PEqualNP.Outside.L_meta_32063.L853.R017.Matched mate color Finset.univ f) :
    ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, f (Fin.append x y) = invFunction p x y := by
  obtain ⟨p, hp, he⟩ := ro_equality_normal_form f hf hm
  refine ⟨p, ⟨hp, he⟩, ?_⟩
  intro q hq
  apply invFunction_injective q p hq.1 hp
  intro x y
  exact (hq.2 x y).symm.trans (he x y)

end PEqualNP.Outside.L_meta_32063.L853.R017.RowColumn

namespace PEqualNP.Outside.L_meta_32063.L853.R017.RowColumn
open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath
variable {k : ℕ}

theorem exists_other (hk : 2 ≤ k) (i : Fin k) : ∃ j : Fin k, j ≠ i := by
  let z : Fin k := ⟨0, by omega⟩
  let o : Fin k := ⟨1, by omega⟩
  by_cases hi : i = z
  · refine ⟨o, ?_⟩
    intro h
    have hv := congrArg Fin.val (h.trans hi)
    change 1 = 0 at hv
    omega
  · exact ⟨z, Ne.symm hi⟩

theorem equality_matched (hk : 2 ≤ k) (f : (Fin (k+k) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hrep : ∀ i j : Fin k, f (pair (row i) (col j)) = decide (i = j)) :
    PEqualNP.Outside.L_meta_32063.L853.R017.Matched mate color Finset.univ f := by
  have hs : PEqualNP.Outside.L_meta_32063.L853.R017.NoSingle f := by
    intro v
    apply Bool.eq_false_iff.mpr
    intro htrue
    induction v using Fin.addCases with
    | left i =>
      obtain ⟨j, hji⟩ := exists_other hk i
      have hx := hmono (single (row i)) (pair (row i) (col j)) (by
        intro t ht
        have he : t = row i := by simpa [single] using ht
        simp [pair, he]) htrue
      rw [hrep, decide_eq_false (Ne.symm hji)] at hx
      contradiction
    | right i =>
      obtain ⟨j, hji⟩ := exists_other hk i
      have hx := hmono (single (col i)) (pair (row j) (col i)) (by
        intro t ht
        have he : t = col i := by simpa [single] using ht
        simp [pair, he]) htrue
      rw [hrep, decide_eq_false hji] at hx
      contradiction
  refine ⟨hs, by simp, ?_, ?_⟩
  · intro v hv
    induction v using Fin.addCases with
    | left i =>
      change f (pair (row i) (mate (row i))) = true
      rw [mate_row, hrep]
      simp
    | right i =>
      change f (pair (col i) (mate (col i))) = true
      rw [mate_col, pair_comm, hrep]
      simp
  · intro v w hc hne
    induction v using Fin.addCases with
    | left i =>
      induction w using Fin.addCases with
      | left j => exact False.elim (hc ((color_row i).trans (color_row j).symm))
      | right j =>
        change col j ≠ mate (row i) at hne
        rw [mate_row] at hne
        have hij : i ≠ j := fun h => hne (congrArg col h.symm)
        rw [hrep, decide_eq_false hij]
    | right i =>
      induction w using Fin.addCases with
      | left j =>
        change row j ≠ mate (col i) at hne
        rw [mate_col] at hne
        have hji : j ≠ i := fun h => hne (congrArg row h)
        rw [pair_comm, hrep, decide_eq_false hji]
      | right j => exact False.elim (hc ((color_col i).trans (color_col j).symm))

theorem equality_ro_classification (hk : 2 ≤ k) (f : (Fin (k+k) → Bool) → Bool)
    (hf : RO Finset.univ f)
    (hrep : ∀ i j : Fin k, f (pair (row i) (col j)) = decide (i = j)) :
    ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, f (Fin.append x y) = invFunction p x y := by
  exact ro_equality_unique_normal_form f hf (equality_matched hk f (ro_mono hf) hrep)

end PEqualNP.Outside.L_meta_32063.L853.R017.RowColumn

namespace PEqualNP.Outside.L_meta_32063.L853.R017.CircuitForward

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath
open PEqualNP.Outside.L_meta_32063.L853.R017.RowColumn

theorem eval_gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi
    exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hi hv⟩

theorem wiresFrom_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, w.length = w'.length →
    (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (wiresFrom gs w).getD i false = true → (wiresFrom gs w').getD i false = true := by
  induction gs with
  | nil => intro w w' hl h; exact h
  | cons g gs ih =>
    intro w w' hl h i hi
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
      (w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)])
      (w' ++ [g.op.eval (g.inputs.map fun a => w'.getD a false)]) (by simp [hl]) ?_ i hi
    intro j hj
    by_cases he : j = w.length
    · rw [he, getD_snoc_eq] at hj
      rw [he, hl, getD_snoc_eq]
      exact eval_gate_mono g (hm g List.mem_cons_self) w w' (fun a _ => h a) hj
    · rw [getD_snoc_ne _ _ _ _ he] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

theorem circuit_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true)
    (he : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
  apply wiresFrom_mono C.gates (fun g hg => (hm g hg).1)
    (List.ofFn x) (List.ofFn y) (by simp) ?_ C.output he
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = true := by simpa [hjn] using hj
    simpa [hjn] using h ⟨j, hjn⟩ hx
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    contradiction

theorem ofFn_pair_row_col {k : ℕ} (i j : Fin k) :
    List.ofFn (pair (row i) (col j)) = oneEach i j := by
  have h : pair (row i) (col j) =
      Fin.append (single i) (single j) := by
    funext v
    induction v using Fin.addCases with
    | left t =>
      have hne : row t ≠ col j := by
        intro h
        have hval := congrArg (fun z : Fin (k+k) => z.val) h
        change t.val = k + j.val at hval
        omega
      simp only [pair, single, Fin.append_left]
      simp only [hne, or_false]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using row_injective.eq_iff)
    | right t =>
      have hne : col t ≠ row i := by
        intro h
        have hval := congrArg (fun z : Fin (k+k) => z.val) h
        change k + t.val = i.val at hval
        omega
      simp only [pair, single, Fin.append_right]
      simp only [hne, false_or]
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using col_injective.eq_iff)
  rw [h, List.ofFn_fin_append]
  rfl

theorem equality_read_once {k : ℕ} (hk : 2 ≤ k) (C : Circuit)
    (hm : Monotone2 C) (hsize : C.size + 1 ≤ 2*k)
    (hrep : Represents (fun i j : Fin k => decide (i = j)) C) :
    RO Finset.univ (fun x : Fin (k+k) → Bool => C.eval (List.ofFn x)) := by
  let f : (Fin (k+k) → Bool) → Bool := fun x => C.eval (List.ofFn x)
  have hrep' : ∀ i j : Fin k, f (pair (row i) (col j)) = decide (i = j) := by
    intro i j
    exact (congrArg C.eval (ofFn_pair_row_col i j)).trans (hrep i j)
  have hm' := equality_matched hk f (circuit_mono C hm) hrep'
  have hsens : ∀ i ∈ (Finset.univ : Finset (Fin (k+k))),
      ∃ x y : Fin (k+k) → Bool, (∀ j, j ≠ i → x j = y j) ∧
        (C.wires (List.ofFn x)).getD C.output false ≠
          (C.wires (List.ofFn y)).getD C.output false := by
    intro i hi
    refine ⟨pair i (mate i), single (mate i), ?_, ?_⟩
    · intro j hji
      simp [pair, single, hji]
    · change f (pair i (mate i)) ≠ f (single (mate i))
      rw [hm'.2.2.1 i hi, hm'.1 (mate i)]
      decide
  have hvalid : C.output < (k+k) + C.gates.length := by
    let z : Fin k := ⟨0, by omega⟩
    have ht := hrep' z z
    have ht' : (C.wires (List.ofFn (pair (row z) (col z)))).getD C.output false = true := by
      change f (pair (row z) (col z)) = true
      simpa only [decide_true] using ht
    by_contra hn
    have hl : (C.wires (List.ofFn (pair (row z) (col z)))).length = (k+k) + C.gates.length := by
      rw [wires_eq, length_wiresFrom]
      simp
    rw [List.getD_eq_default _ _ (by omega)] at ht'
    contradiction
  have hb := wire_essential_bound C (k+k) C.gates.length C.output le_rfl hvalid
    (fun g hg => (hm g hg).2) Finset.univ hsens
  have hcard : (Finset.univ : Finset (Fin (k+k))).card = C.gates.length + 1 := by
    simp only [Finset.card_univ, Fintype.card_fin] at hb ⊢
    change C.gates.length + 1 ≤ 2*k at hsize
    omega
  exact wire_read_once C (k+k) C.gates.length C.output le_rfl hvalid
    (fun g hg => ⟨by have h := (hm g hg).1; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h; tauto, (hm g hg).2⟩)
    Finset.univ hcard hsens

theorem equality_circuit_classification {k : ℕ} (hk : 2 ≤ k) (C : Circuit)
    (hm : Monotone2 C) (hsize : C.size + 1 ≤ 2*k)
    (hrep : Represents (fun i j : Fin k => decide (i = j)) C) :
    ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = invFunction p x y := by
  have h := equality_ro_classification hk
    (fun x : Fin (k+k) → Bool => C.eval (List.ofFn x))
    (equality_read_once hk C hm hsize hrep) (by
      intro i j
      rw [ofFn_pair_row_col]
      exact hrep i j)
  simpa only [List.ofFn_fin_append] using h

end PEqualNP.Outside.L_meta_32063.L853.R017.CircuitForward

namespace PEqualNP.Outside.L_meta_32063.L853.R017

 theorem official_forward : ∀ (k : Nat), 2 ≤ k → ∀ f : (Fin k → Bool) → (Fin k → Bool) → Bool,
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2*k ∧
    PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) →
  ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
    ∀ x y, f x y = decide (∃ i : Fin k,
        (x i = true ∧ y i = true) ∨
        (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨
          (y i = true ∧ y (p i) = true)))) := by
  intro k hk f h
  obtain ⟨C, hm, hs, hr, he⟩ := h
  obtain ⟨p, hp, hu⟩ := CircuitForward.equality_circuit_classification hk C hm hs hr
  refine ⟨p, ⟨hp.1, ?_⟩, ?_⟩
  · intro x y
    exact (he x y).trans (hp.2 x y)
  · intro q hq
    apply hu q
    refine ⟨hq.1, ?_⟩
    intro x y
    exact (he x y).symm.trans (hq.2 x y)

end PEqualNP.Outside.L_meta_32063.L853.R017

namespace PEqualNP.Outside.L_meta_32063.L853.R020.ROCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce

variable {n : ℕ}

def GateOK (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def Compiled (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ m : ℕ, n ≤ m → ∃ (gs : List Gate) (out : ℕ),
    (∀ g ∈ gs, GateOK g) ∧ gs.length + 1 = S.card ∧ out < m + gs.length ∧
    ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = f (fun i : Fin n => w.getD i.val false)

theorem compiled_leaf (i : Fin n) : Compiled {i} (fun x => x i) := by
  intro m hm
  refine ⟨[], i.val, ?_, by simp, ?_, ?_⟩
  · simp
  · have := i.isLt
    simp only [List.length_nil, Nat.add_zero]
    omega
  · intro w hw
    rfl

theorem compiled_join {A B : Finset (Fin n)} {a b : (Fin n → Bool) → Bool}
    (hd : Disjoint A B) (ha : Compiled A a) (hb : Compiled B b)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) :
    Compiled (A ∪ B) (fun x => op.eval [a x, b x]) := by
  intro m hm
  obtain ⟨ga, oa, oka, lena, ra, eva⟩ := ha m hm
  obtain ⟨gb, ob, okb, lenb, rb, evb⟩ := hb (m + ga.length) (by omega)
  let M := m + ga.length + gb.length
  refine ⟨ga ++ gb ++ [⟨op, [oa, ob]⟩], M, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact oka g hg
    · exact okb g hg
    · subst g
      exact ⟨hop, by simp⟩
  · rw [Finset.card_union_of_disjoint hd]
    simp only [List.length_append, List.length_singleton]
    omega
  · simp only [List.length_append, List.length_singleton]
    dsimp [M]
    omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    let wa := wiresFrom ga w
    let wb := wiresFrom gb wa
    have hwa : wa.length = m + ga.length := by
      dsimp [wa]
      rw [length_wiresFrom, hw]
    have hwb : wb.length = M := by
      dsimp [wb]
      rw [length_wiresFrom, hwa]
    have eqa : wb.getD oa false = a (fun i : Fin n => w.getD i.val false) := by
      dsimp [wb]
      rw [getD_wiresFrom gb wa oa (by omega)]
      exact eva w hw
    have eqb : wb.getD ob false = b (fun i : Fin n => w.getD i.val false) := by
      dsimp [wb]
      rw [evb wa hwa]
      congr 1
      funext i
      exact getD_wiresFrom ga w i.val (by have := i.isLt; omega)
    change (wiresFrom [⟨op, [oa, ob]⟩] wb).getD M false = _
    change (wb ++ [op.eval [wb.getD oa false, wb.getD ob false]]).getD M false = _
    rw [← hwb, getD_snoc_eq, eqa, eqb]

theorem ro_compiled {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (h : RO S f) : Compiled S f := by
  apply h Compiled compiled_leaf
  intro A B a b hd ha hb
  constructor
  · simpa only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, id_eq]
      using compiled_join hd ha hb GateOp.and (Or.inl rfl)
  · simpa only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      using compiled_join hd ha hb GateOp.or (Or.inr rfl)

theorem ro_circuit {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (h : RO S f) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 = S.card ∧ C.output < n + C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  obtain ⟨gs, out, hok, hlen, hout, heval⟩ := ro_compiled h n (le_refl n)
  refine ⟨⟨gs, out⟩, ?_, hlen, hout, ?_⟩
  · intro g hg
    obtain ⟨ho, hl⟩ := hok g hg
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩
  · intro x
    change (wiresFrom gs (List.ofFn x)).getD out false = f x
    rw [heval (List.ofFn x) (by simp)]
    congr 1
    funext i
    simp

theorem ro_circuit_exists {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool}
    (h : RO S f) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 = S.card ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  obtain ⟨C, hC, hsize, _, heval⟩ := ro_circuit h
  exact ⟨C, hC, hsize, heval⟩

end PEqualNP.Outside.L_meta_32063.L853.R020.ROCompiler

namespace PEqualNP.Outside.L_meta_32063.L853.R019.InvolutionRO

open PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath PEqualNP.Outside.L_meta_32063.L853.R017.RowColumn

variable {k : ℕ}

theorem row_ne_col (i j : Fin k) : row i ≠ col j := by
  intro h
  have e := congrArg (fun z : Fin (k+k) => z.val) h
  change i.val = k + j.val at e
  omega

theorem col_ne_row (i j : Fin k) : col i ≠ row j := (row_ne_col j i).symm

def supp (S : Finset (Fin k)) : Finset (Fin (k+k)) := S.image row ∪ S.image col

def clause (p : Equiv.Perm (Fin k)) (i : Fin k) (x : Fin (k+k) → Bool) : Prop :=
  (x (row i) = true ∧ x (col i) = true) ∨
  (p i ≠ i ∧ ((x (row i) = true ∧ x (row (p i)) = true) ∨
    (x (col i) = true ∧ x (col (p i)) = true)))

noncomputable def evalOn (p : Equiv.Perm (Fin k)) (S : Finset (Fin k))
    (x : Fin (k+k) → Bool) : Bool := by
  classical
  exact decide (∃ i ∈ S, clause p i x)

theorem supp_union (S T : Finset (Fin k)) : supp (S ∪ T) = supp S ∪ supp T := by
  classical
  ext i
  simp only [supp, Finset.mem_union, Finset.mem_image]
  aesop

theorem supp_disjoint {S T : Finset (Fin k)} (hd : Disjoint S T) :
    Disjoint (supp S) (supp T) := by
  classical
  rw [Finset.disjoint_left] at hd ⊢
  intro v hv hw
  simp only [supp, Finset.mem_union, Finset.mem_image] at hv hw
  rcases hv with ⟨i,hi,rfl⟩ | ⟨i,hi,rfl⟩
  · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
    · exact hd hi ((row_injective he) ▸ hj)
    · exact col_ne_row j i he
  · rcases hw with ⟨j,hj,he⟩ | ⟨j,hj,he⟩
    · exact row_ne_col j i he
    · exact hd hi ((col_injective he) ▸ hj)

theorem evalOn_union (p : Equiv.Perm (Fin k)) (S T : Finset (Fin k)) :
    evalOn p (S ∪ T) = fun x => evalOn p S x || evalOn p T x := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [evalOn, decide_eq_true_eq, Bool.or_eq_true, Finset.mem_union]
  aesop

theorem fixed_ro (p : Equiv.Perm (Fin k)) (i : Fin k) (hi : p i = i) :
    RO (supp {i}) (evalOn p {i}) := by
  have hr := ro_and (by simpa using row_ne_col i i) (ro_leaf (row i)) (ro_leaf (col i))
  convert hr using 1
  · simp [supp]
  · funext x
    simp [evalOn, clause, hi]

theorem pair_ro (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (i j : Fin k) (hij : i ≠ j) (hpij : p i = j) :
    RO (supp {i,j}) (evalOn p {i,j}) := by
  have hpji : p j = i := by rw [← hpij, hp i]
  have hA := ro_or (by simpa using row_ne_col i j) (ro_leaf (row i)) (ro_leaf (col j))
  have hB := ro_or (by simpa using col_ne_row i j) (ro_leaf (col i)) (ro_leaf (row j))
  have hd : Disjoint (({row i} ∪ {col j}) : Finset (Fin (k+k))) ({col i} ∪ {row j}) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    simp only [Finset.mem_union, Finset.mem_singleton] at hv hw
    rcases hv with rfl | rfl
    · rcases hw with he | he
      · exact row_ne_col i i he
      · exact hij (row_injective he)
    · rcases hw with he | he
      · exact hij.symm (col_injective he)
      · exact col_ne_row j j he
  have hr := ro_and hd hA hB
  convert hr using 1
  · ext v
    simp only [supp, Finset.image_insert, Finset.image_singleton, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  · funext x
    apply Bool.eq_iff_iff.mpr
    simp only [evalOn, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton,
      exists_eq_or_imp, exists_eq_left, clause, hpij, hpji, Bool.and_eq_true, Bool.or_eq_true]
    tauto

theorem union_ro (p : Equiv.Perm (Fin k)) (S T : Finset (Fin k))
    (hd : Disjoint S T) (hS : RO (supp S) (evalOn p S)) (hT : RO (supp T) (evalOn p T)) :
    RO (supp (S ∪ T)) (evalOn p (S ∪ T)) := by
  rw [supp_union, evalOn_union]
  exact ro_or (supp_disjoint hd) hS hT

theorem invariant_ro (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (S : Finset (Fin k)) (hS : ∀ i ∈ S, p i ∈ S) (hne : S.Nonempty) :
    RO (supp S) (evalOn p S) := by
  classical
  revert hS hne
  refine Finset.strongInductionOn S ?_
  intro S ih hS hne
  obtain ⟨i, hi⟩ := hne
  by_cases hfix : p i = i
  · let T := S.erase i
    have ht : T ⊂ S := Finset.erase_ssubset hi
    have hclose : ∀ j ∈ T, p j ∈ T := by
      intro j hj
      have hjs := Finset.mem_erase.mp hj
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        apply hjs.1
        exact p.injective (he.trans hfix.symm)
      · exact hS j hjs.2
    have heq : S = {i} ∪ T := by simp [T, hi]
    by_cases hempty : T = ∅
    · rw [heq, hempty, Finset.union_empty]
      exact fixed_ro p i hfix
    · rw [heq]
      apply union_ro p {i} T
      · simp [T]
      · exact fixed_ro p i hfix
      · exact ih T ht hclose (Finset.nonempty_iff_ne_empty.mpr hempty)
  · let j := p i
    have hij : i ≠ j := Ne.symm hfix
    have hj : j ∈ S := hS i hi
    have hpji : p j = i := hp i
    let T := (S.erase i).erase j
    have ht : T ⊂ S :=
      lt_of_le_of_lt (Finset.erase_subset j (S.erase i)) (Finset.erase_ssubset hi)
    have hclose : ∀ a ∈ T, p a ∈ T := by
      intro a ha
      have h := Finset.mem_erase.mp ha
      have h' := Finset.mem_erase.mp h.2
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        exact h'.1 (p.injective he)
      · apply Finset.mem_erase.mpr
        constructor
        · intro he
          exact h.1 (p.injective (he.trans hpji.symm))
        · exact hS a h'.2
    have heq : S = {i,j} ∪ T := by
      ext a
      simp only [T, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_erase]
      constructor
      · intro ha
        by_cases hai : a = i
        · exact Or.inl (Or.inl hai)
        · by_cases haj : a = j
          · exact Or.inl (Or.inr haj)
          · exact Or.inr ⟨haj,hai,ha⟩
      · rintro ((rfl | rfl) | ⟨-, -, ha⟩)
        · exact hi
        · exact hj
        · exact ha
    by_cases hempty : T = ∅
    · rw [heq, hempty, Finset.union_empty]
      exact pair_ro p hp i j hij rfl
    · rw [heq]
      apply union_ro p {i,j} T
      · simp [T, Finset.disjoint_left]
      · exact pair_ro p hp i j hij rfl
      · exact ih T ht hclose (Finset.nonempty_iff_ne_empty.mpr hempty)

theorem involution_ro (hk : 0 < k) (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    RO Finset.univ (fun x : Fin (k+k) → Bool => invFunction p (fun i => x (row i))
      (fun i => x (col i))) := by
  have h := invariant_ro p hp Finset.univ (by simp) ⟨⟨0,hk⟩,Finset.mem_univ _⟩
  have hs : supp (Finset.univ : Finset (Fin k)) = Finset.univ := by
    ext v
    simp only [Finset.mem_univ, iff_true]
    induction v using Fin.addCases with
    | left i => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    | right i => exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  rw [hs] at h
  have he : evalOn p Finset.univ = (fun x : Fin (k+k) → Bool => invFunction p (fun i => x (row i)) (fun i => x (col i))) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [evalOn, clause, invFunction]
  rw [he] at h
  exact h

end PEqualNP.Outside.L_meta_32063.L853.R019.InvolutionRO

namespace PEqualNP.Outside.L_meta_32063.L853.R019.InverseBridge
open PEqualNP.Outside.L_meta_32063.L853.R017.RowColumn PEqualNP.Outside.L_meta_32063.L853.R012.TightReadOnce PEqualNP.Outside.L_meta_32063.L853.R012.ReadOncePath
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem invFunction_oneEach {k : ℕ} (p : Equiv.Perm (Fin k)) (i j : Fin k) :
    invFunction p (single i) (single j) = decide (i = j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [invFunction, single, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ⟨hai,haj⟩ | ⟨hne,h | h⟩⟩
    · exact hai.symm.trans haj
    · exact False.elim (hne (h.2.trans h.1.symm))
    · exact False.elim (hne (h.2.trans h.1.symm))
  · intro hij
    exact ⟨i,Or.inl ⟨rfl,hij⟩⟩

theorem involution_circuit_of_compiler
    (compileRO : ∀ {n : ℕ} {S : Finset (Fin n)} {f : (Fin n → Bool) → Bool},
      RO S f → ∃ C : Circuit, Monotone2 C ∧ C.size + 1 = S.card ∧
        ∀ x, C.eval (List.ofFn x) = f x)
    {k : ℕ} (hk : 0 < k) (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ 2*k ∧
      Represents (fun i j : Fin k => decide (i = j)) C ∧
      ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = invFunction p x y := by
  obtain ⟨C, hm, hs, he⟩ := compileRO (InvolutionRO.involution_ro hk p hp)
  have hfull : ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = invFunction p x y := by
    intro x y
    simpa only [List.ofFn_fin_append, Fin.append_left, Fin.append_right]
      using he (Fin.append x y)
  refine ⟨C,hm,?_,?_,hfull⟩
  · simp only [Finset.card_univ, Fintype.card_fin] at hs
    omega
  · intro i j
    change C.eval (List.ofFn (single i) ++ List.ofFn (single j)) = decide (i = j)
    rw [hfull, invFunction_oneEach]

end PEqualNP.Outside.L_meta_32063.L853.R019.InverseBridge

namespace PEqualNP.Outside.L_meta_32063.L853.R019

theorem official_full : ∀ (k : Nat), 2 ≤ k → ∀ f : (Fin k → Bool) → (Fin k → Bool) → Bool,
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2*k ∧
    PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ↔
  ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
    ∀ x y, f x y = decide (∃ i : Fin k,
        (x i = true ∧ y i = true) ∨
        (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨
          (y i = true ∧ y (p i) = true)))) := by
  intro k hk f
  constructor
  · exact PEqualNP.Outside.L_meta_32063.L853.R017.official_forward k hk f
  · rintro ⟨p, ⟨hp, hf⟩, hu⟩
    obtain ⟨C, hm, hs, hr, he⟩ := InverseBridge.involution_circuit_of_compiler
      (fun h => PEqualNP.Outside.L_meta_32063.L853.R020.ROCompiler.ro_circuit_exists h) (by omega : 0 < k) p hp
    refine ⟨C, hm, hs, hr, ?_⟩
    intro x y
    exact (hf x y).trans (he x y).symm

end PEqualNP.Outside.L_meta_32063.L853.R019

namespace PEqualNP.Outside.L_meta_32063.L924

def NC (n : ℕ) : Finset (Finset ℕ) := (Finset.range n).powerset.filter (fun I => ∀ i ∈ I, i + 1 ∉ I)

theorem NC_succ_succ (n : ℕ) : (NC (n + 2)).card = (NC (n + 1)).card + (NC n).card := by
  rw [← Finset.card_filter_add_card_filter_not (fun I => n + 1 ∈ I), add_comm (NC (n + 1)).card]
  congr 1
  ·
    symm
    refine Finset.card_bij' (fun J _ => insert (n + 1) J) (fun I _ => I.erase (n + 1)) ?_ ?_ ?_ ?_
    · intro J hJ
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hJ ⊢
      obtain ⟨hs, hc⟩ := hJ
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hi); omega)
      · intro i hi h2
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rcases Finset.mem_insert.mp h2 with h | h
          · omega
          · have := Finset.mem_range.mp (hs h); omega
        · rcases Finset.mem_insert.mp h2 with h | h
          · have hlt : i < n := Finset.mem_range.mp (hs hi)
            have hieq : i = n := by omega
            exact absurd hlt (by omega)
          · exact hc i hi h
    · intro I hI
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hI ⊢
      obtain ⟨⟨hs, hc⟩, hn⟩ := hI
      refine ⟨fun i hi => ?_, fun i hi h2 => hc i (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase h2)⟩
      have hne := Finset.ne_of_mem_erase hi
      have hi' := Finset.mem_of_mem_erase hi
      have hr := Finset.mem_range.mp (hs hi')
      have : i ≠ n := fun h => hc i hi' (h ▸ hn)
      exact Finset.mem_range.mpr (by omega)
    · intro J hJ
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hJ
      apply Finset.erase_insert
      intro h; have := Finset.mem_range.mp (hJ.1 h); omega
    · intro I hI
      simp only [Finset.mem_filter] at hI
      exact Finset.insert_erase hI.2
  ·
    congr 1
    ext I
    simp only [NC, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hs, hc⟩, hn⟩
      refine ⟨fun i hi => ?_, hc⟩
      have hlt : i < n + 2 := Finset.mem_range.mp (hs hi)
      have hne : i ≠ n + 1 := fun h => hn (h ▸ hi)
      exact Finset.mem_range.mpr (by omega)
    · rintro ⟨hs, hc⟩
      refine ⟨⟨fun i hi => Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hi); omega), hc⟩, fun h => ?_⟩
      have := Finset.mem_range.mp (hs h); omega

theorem NC_card (n : ℕ) : (NC n).card = Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | k + 2 =>
      rw [NC_succ_succ, ih (k + 1) (by omega), ih k (by omega)]
      have h := Nat.fib_add_two (n := k + 2)
      rw [show k + 2 + 2 = k + 2 + 2 from rfl, h, show k + 1 + 2 = k + 2 + 1 from rfl]
      ring

theorem NC_avoid0_card (n : ℕ) : ((NC n).filter (fun I => 0 ∉ I)).card = Nat.fib (n + 1) := by
  match n with
  | 0 => decide
  | k + 1 =>
    rw [show k + 1 + 1 = k + 2 from rfl, ← NC_card k]
    symm
    refine Finset.card_bij' (fun J _ => J.image (· + 1)) (fun I _ => I.image (· - 1)) ?_ ?_ ?_ ?_
    · intro J hJ
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hJ
      obtain ⟨hs, hc⟩ := hJ
      simp only [NC, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hj); omega)
      · intro i hi h2
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨j', hj', h⟩ := Finset.mem_image.mp h2
        exact hc j hj (by rw [show j + 1 = j' by omega]; exact hj')
      · intro h; obtain ⟨j, _, h⟩ := Finset.mem_image.mp h; omega
    · intro I hI
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hI
      obtain ⟨⟨hs, hc⟩, h0⟩ := hI
      simp only [NC, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        have hj0 : j ≠ 0 := fun h => h0 (h ▸ hj)
        exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hj); omega)
      · intro i hi h2
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨j', hj', h⟩ := Finset.mem_image.mp h2
        have hj0 : j ≠ 0 := fun h => h0 (h ▸ hj)
        have hj0' : j' ≠ 0 := fun h => h0 (h ▸ hj')
        exact hc j hj (by rw [show j + 1 = j' by omega]; exact hj')
    · intro J hJ
      ext i
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨j, ⟨j', hj', rfl⟩, rfl⟩; simpa using hj'
      · intro hi; exact ⟨i + 1, ⟨i, hi, rfl⟩, by omega⟩
    · intro I hI
      simp only [NC, Finset.mem_filter] at hI
      ext i
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨j, ⟨j', hj', rfl⟩, rfl⟩
        have hj0 : j' ≠ 0 := fun h => hI.2 (h ▸ hj')
        rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
      · intro hi
        have : i ≠ 0 := fun h => hI.2 (h ▸ hi)
        exact ⟨i - 1, ⟨i, hi, rfl⟩, by omega⟩

theorem cassini_even (k : ℕ) : Nat.fib (2 * k + 1) ^ 2 = Nat.fib (2 * k) * Nat.fib (2 * k + 2) + 1 := by
  have h : ∀ n : ℕ, (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by exact_mod_cast Nat.fib_add_two
      have e2 : (Nat.fib (n + 1 + 2) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by exact_mod_cast Nat.fib_add_two
      rw [show n + 1 + 1 = n + 2 by ring, e2, pow_succ (-1 : ℤ) n, ← ih, e1]; ring
  have := h (2 * k)
  rw [pow_mul, show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_pow] at this
  have : (Nat.fib (2 * k + 1) : ℤ) ^ 2 = Nat.fib (2 * k) * Nat.fib (2 * k + 2) + 1 := by linarith
  exact_mod_cast this

abbrev good (C : Finset ℕ) (I : Finset (ℕ × ℕ)) : Prop :=
  (∀ z ∈ I, (z.1, z.2 + 1) ∉ I) ∧ (∀ x ∈ C, (x, 0) ∉ I)

def Gset (v L : ℕ) (C : Finset ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((Finset.range v ×ˢ Finset.range L).powerset).filter (good C)

def blk (L : ℕ) (C : Finset ℕ) (x : ℕ) : Finset (Finset ℕ) :=
  if x ∈ C then (NC L).filter (fun I => 0 ∉ I) else NC L

theorem blk_card (L : ℕ) (C : Finset ℕ) (x : ℕ) :
    (blk L C x).card = if x ∈ C then Nat.fib (L + 1) else Nat.fib (L + 2) := by
  unfold blk; split_ifs
  · exact NC_avoid0_card L
  · exact NC_card L

theorem Gset_succ (v L : ℕ) (C : Finset ℕ) :
    (Gset (v + 1) L C).card = (Gset v L C).card * (blk L C v).card := by
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun I _ => (I.filter (fun z => z.1 < v), (I.filter (fun z => z.1 = v)).image Prod.snd))
    (fun p _ => p.1 ∪ p.2.image (fun i => (v, i))) ?_ ?_ ?_ ?_
  · intro I hI
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset] at hI
    obtain ⟨hs, hc, h0⟩ := hI
    simp only [Finset.mem_product, Gset, good, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro z hz
      obtain ⟨hz, hlt⟩ := Finset.mem_filter.mp hz
      have := Finset.mem_product.mp (hs hz)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hlt, this.2⟩
    · intro z hz h2
      exact hc z hz.1 h2.1
    · intro x hx h2
      exact h0 x hx h2.1
    · unfold blk
      have hsub : (I.filter (fun z => z.1 = v)).image Prod.snd ⊆ Finset.range L := by
        intro i hi
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_product.mp (hs (Finset.mem_filter.mp hz).1)).2
      have hnc : (I.filter (fun z => z.1 = v)).image Prod.snd ∈ NC L := by
        simp only [NC, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨hsub, fun i hi h2 => ?_⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨z', hz', h'⟩ := Finset.mem_image.mp h2
        obtain ⟨hzI, hz1⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzI', hz1'⟩ := Finset.mem_filter.mp hz'
        apply hc z hzI
        have : z' = (z.1, z.2 + 1) := Prod.ext (by omega) h'
        rw [← this]; exact hzI'
      split_ifs with hv
      · refine Finset.mem_filter.mpr ⟨hnc, fun h => ?_⟩
        obtain ⟨z, hz, h'⟩ := Finset.mem_image.mp h
        obtain ⟨hzI, hz1⟩ := Finset.mem_filter.mp hz
        apply h0 v hv
        have : z = (v, 0) := Prod.ext hz1 h'
        rw [← this]; exact hzI
      · exact hnc
  · intro p hp
    obtain ⟨hJ, hK⟩ := Finset.mem_product.mp hp
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset] at hJ
    obtain ⟨hs, hc, h0⟩ := hJ
    have hK' : p.2 ∈ NC L ∧ (v ∈ C → 0 ∉ p.2) := by
      unfold blk at hK; split_ifs at hK with hv
      · exact ⟨(Finset.mem_filter.mp hK).1, fun _ => (Finset.mem_filter.mp hK).2⟩
      · exact ⟨hK, fun h => absurd h hv⟩
    obtain ⟨hKnc, hK0⟩ := hK'
    simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hKnc
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.mp hz with h | h
      · have := Finset.mem_product.mp (hs h)
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp this.1; omega), this.2⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), hKnc.1 hi⟩
    · intro z hz h2
      rcases Finset.mem_union.mp hz with h | h
      · rcases Finset.mem_union.mp h2 with h' | h'
        · exact hc z h h'
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h'
          have h1 : z.1 = v := (congrArg Prod.fst hi).symm
          have := Finset.mem_range.mp (Finset.mem_product.mp (hs h)).1
          omega
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        rcases Finset.mem_union.mp h2 with h' | h'
        · have := Finset.mem_range.mp (Finset.mem_product.mp (hs h')).1
          simp at this
        · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h'
          have : j = i + 1 := congrArg Prod.snd hji
          exact hKnc.2 i hi (this ▸ hj)
    · intro x hx h2
      rcases Finset.mem_union.mp h2 with h | h
      · exact h0 x hx h
      · obtain ⟨i, hi, hxi⟩ := Finset.mem_image.mp h
        have e1 : v = x := congrArg Prod.fst hxi
        have e2 : i = 0 := congrArg Prod.snd hxi
        exact hK0 (e1 ▸ hx) (e2 ▸ hi)
  · intro I hI
    simp only [Gset, Finset.mem_filter, Finset.mem_powerset] at hI
    ext z
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro (⟨hz, _⟩ | ⟨i, ⟨w, ⟨hw, hw1⟩, rfl⟩, rfl⟩)
      · exact hz
      · rw [← hw1]; exact hw
    · intro hz
      have := Finset.mem_range.mp (Finset.mem_product.mp (hI.1 hz)).1
      rcases Nat.lt_or_ge z.1 v with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨z.2, ⟨z, ⟨hz, by omega⟩, rfl⟩, Prod.ext (by omega) rfl⟩
  · intro p hp
    obtain ⟨hJ, hK⟩ := Finset.mem_product.mp hp
    simp only [Gset, Finset.mem_filter, Finset.mem_powerset] at hJ
    refine Prod.ext ?_ ?_
    · ext z
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨h | ⟨i, _, rfl⟩, hlt⟩
        · exact h
        · simp at hlt
      · intro hz
        exact ⟨Or.inl hz, Finset.mem_range.mp (Finset.mem_product.mp (hJ.1 hz)).1⟩
    · ext i
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨z, ⟨h | ⟨j, hj, rfl⟩, hz1⟩, rfl⟩
        · have := Finset.mem_range.mp (Finset.mem_product.mp (hJ.1 h)).1; omega
        · exact hj
      · intro hi; exact ⟨(v, i), ⟨Or.inr ⟨i, hi, rfl⟩, rfl⟩, rfl⟩

theorem Gset_card (v L : ℕ) (C : Finset ℕ) :
    (Gset v L C).card = ∏ x ∈ Finset.range v, (if x ∈ C then Nat.fib (L + 1) else Nat.fib (L + 2)) := by
  induction v with
  | zero =>
    have : Finset.filter (good C) {∅} = {∅} := Finset.filter_true_of_mem (fun I hI => by
      rw [Finset.mem_singleton.mp hI]; exact ⟨fun z hz => absurd hz (Finset.notMem_empty z), fun x _ h => absurd h (Finset.notMem_empty _)⟩)
    simp [Gset, this]
  | succ v ih => rw [Gset_succ, ih, Finset.prod_range_succ, blk_card]

theorem Gset_card' (v L : ℕ) (C : Finset ℕ) (hC : C ⊆ Finset.range v) :
    (Gset v L C).card = Nat.fib (L + 1) ^ C.card * Nat.fib (L + 2) ^ (v - C.card) := by
  rw [Gset_card, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.range v).filter (fun x => x ∈ C) = C := by
    ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hC h, h⟩⟩
  have h2 : ((Finset.range v).filter (fun x => x ∉ C)).card = v - C.card := by
    rw [Finset.filter_not, Finset.card_sdiff, h1, Finset.inter_eq_left.mpr hC, Finset.card_range]
  rw [h1, h2]

def verts (e : ℕ × ℕ) : Finset ℕ := {e.1, e.2}
abbrev IsMatch (S : Finset (ℕ × ℕ)) : Prop := ∀ e ∈ S, ∀ g ∈ S, e ≠ g → Disjoint (verts e) (verts g)
def lift (L : ℕ) (e : ℕ × ℕ) : ℕ × ℕ := (e.1 * (L + 1), e.2 * (L + 1))
def rail (L : ℕ) (z : ℕ × ℕ) : ℕ × ℕ := (z.1 * (L + 1) + z.2, z.1 * (L + 1) + z.2 + 1)
def cov (S : Finset (ℕ × ℕ)) : Finset ℕ := S.biUnion verts

theorem dm (L x i : ℕ) (hi : i < L + 1) : (x * (L + 1) + i) / (L + 1) = x ∧ (x * (L + 1) + i) % (L + 1) = i := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hi

theorem blk_eq {L x y i j : ℕ} (hi : i < L + 1) (hj : j < L + 1) (h : x * (L + 1) + i = y * (L + 1) + j) :
    x = y ∧ i = j := by
  obtain ⟨a1, a2⟩ := dm L x i hi
  obtain ⟨b1, b2⟩ := dm L y j hj
  rw [h] at a1 a2
  exact ⟨a1.symm.trans b1, a2.symm.trans b2⟩

theorem not_disj {a b c d : ℕ} (h : ¬ Disjoint ({a, b} : Finset ℕ) {c, d}) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra hn
  push Not at hn
  apply h
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h' | h' <;> simp_all

theorem disj_of {a b c d : ℕ} (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c) (h4 : b ≠ d) :
    Disjoint ({a, b} : Finset ℕ) {c, d} := by
  by_contra h; rcases not_disj h with h | h | h | h <;> contradiction

theorem rail_rail {L : ℕ} {z w : ℕ × ℕ} (hz : z.2 < L) (hw : w.2 < L) (hne : z ≠ w)
    (h : ¬ Disjoint (verts (rail L z)) (verts (rail L w))) :
    (w = (z.1, z.2 + 1)) ∨ (z = (w.1, w.2 + 1)) := by
  simp only [verts, rail] at h
  rcases not_disj h with h | h | h | h
  · exact absurd (Prod.ext (blk_eq (by omega) (by omega) h).1 (blk_eq (by omega) (by omega) h).2) hne
  · have := blk_eq (L := L) (x := z.1) (y := w.1) (i := z.2) (j := w.2 + 1) (by omega) (by omega) (by omega)
    right; exact Prod.ext this.1 this.2
  · have := blk_eq (L := L) (x := z.1) (y := w.1) (i := z.2 + 1) (j := w.2) (by omega) (by omega) (by omega)
    left; exact Prod.ext this.1.symm this.2.symm
  · have := blk_eq (L := L) (x := z.1) (y := w.1) (i := z.2) (j := w.2) (by omega) (by omega) (by omega)
    exact absurd (Prod.ext this.1 this.2) hne

theorem lift_rail {L : ℕ} {e z : ℕ × ℕ} (hz : z.2 < L) (h : ¬ Disjoint (verts (lift L e)) (verts (rail L z))) :
    z.2 = 0 ∧ (z.1 = e.1 ∨ z.1 = e.2) := by
  simp only [verts, lift, rail] at h
  rcases not_disj h with h | h | h | h
  · have := blk_eq (L := L) (x := e.1) (y := z.1) (i := 0) (j := z.2) (by omega) (by omega) (by omega)
    exact ⟨this.2.symm, Or.inl this.1.symm⟩
  · have := blk_eq (L := L) (x := e.1) (y := z.1) (i := 0) (j := z.2 + 1) (by omega) (by omega) (by omega); omega
  · have := blk_eq (L := L) (x := e.2) (y := z.1) (i := 0) (j := z.2) (by omega) (by omega) (by omega)
    exact ⟨this.2.symm, Or.inr this.1.symm⟩
  · have := blk_eq (L := L) (x := e.2) (y := z.1) (i := 0) (j := z.2 + 1) (by omega) (by omega) (by omega); omega

theorem lift_ne_rail {L : ℕ} {e z : ℕ × ℕ} (hz : z.2 < L) : lift L e ≠ rail L z := by
  intro h
  simp only [lift, rail, Prod.mk.injEq] at h
  have b := blk_eq (L := L) (x := e.2) (y := z.1) (i := 0) (j := z.2 + 1) (by omega) (by omega) (by omega)
  omega

theorem rail_inj {L : ℕ} {z w : ℕ × ℕ} (hz : z.2 < L) (hw : w.2 < L) (h : rail L z = rail L w) : z = w := by
  simp only [rail, Prod.mk.injEq] at h
  have := blk_eq (L := L) (by omega) (by omega) h.1
  exact Prod.ext this.1 this.2

theorem lift_inj {L : ℕ} {e g : ℕ × ℕ} (h : lift L e = lift L g) : e = g := by
  simp only [lift, Prod.mk.injEq] at h
  exact Prod.ext (Nat.eq_of_mul_eq_mul_right (by omega) h.1) (Nat.eq_of_mul_eq_mul_right (by omega) h.2)

theorem lift_disj {L : ℕ} {e g : ℕ × ℕ} (h : Disjoint (verts e) (verts g)) : Disjoint (verts (lift L e)) (verts (lift L g)) := by
  simp only [verts, lift]
  have hd : ∀ a b : ℕ, a * (L + 1) = b * (L + 1) → a = b := fun a b h => Nat.eq_of_mul_eq_mul_right (by omega) h
  have h' : ∀ x, x ∈ verts e → x ∉ verts g := fun x hx hg => Finset.disjoint_left.mp h hx hg
  simp only [verts, Finset.mem_insert, Finset.mem_singleton] at h'
  apply disj_of
  · intro hh; exact h' _ (Or.inl rfl) (Or.inl (hd _ _ hh))
  · intro hh; exact h' _ (Or.inl rfl) (Or.inr (hd _ _ hh))
  · intro hh; exact h' _ (Or.inr rfl) (Or.inl (hd _ _ hh))
  · intro hh; exact h' _ (Or.inr rfl) (Or.inr (hd _ _ hh))

theorem lift_disj_rev {L : ℕ} {e g : ℕ × ℕ} (h : Disjoint (verts (lift L e)) (verts (lift L g))) : Disjoint (verts e) (verts g) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hg
  simp only [verts, lift, Finset.mem_insert, Finset.mem_singleton] at hx hg h
  exact h (a := x * (L + 1)) (by rcases hx with rfl | rfl <;> simp) (by rcases hg with rfl | rfl <;> simp)

theorem rail_meet (L : ℕ) (z : ℕ × ℕ) : z.1 * (L + 1) + z.2 + 1 ∈ verts (rail L z) := by simp [verts, rail]

def railsF (v L : ℕ) : Finset (ℕ × ℕ) := (Finset.range v ×ˢ Finset.range L).image (rail L)
def bigF (v L : ℕ) (E : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  ((E.image (lift L)) ∪ railsF v L).powerset.filter IsMatch

theorem fiber_card (v L : ℕ) (E S : Finset (ℕ × ℕ)) (hSE : S ⊆ E) (hS : IsMatch S) :
    ((bigF v L E).filter (fun T => E.filter (fun e => lift L e ∈ T) = S)).card = (Gset v L (cov S)).card := by
  refine Finset.card_bij' (fun T _ => (Finset.range v ×ˢ Finset.range L).filter (fun z => rail L z ∈ T))
    (fun I _ => S.image (lift L) ∪ I.image (rail L)) ?_ ?_ ?_ ?_
  ·
    intro T hT
    simp only [bigF, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨⟨hsub, hm⟩, hS'⟩ := hT
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, ?_, ?_⟩
    · intro z hz hz'
      obtain ⟨hzr, hzT⟩ := hz
      obtain ⟨hzr', hzT'⟩ := hz'
      have hL : z.2 < L := (Finset.mem_product.mp hzr).2 |> Finset.mem_range.mp
      have hL' : z.2 + 1 < L := (Finset.mem_product.mp hzr').2 |> Finset.mem_range.mp
      have hne : rail L z ≠ rail L (z.1, z.2 + 1) := fun h => by
        have := rail_inj (w := (z.1, z.2 + 1)) hL hL' h
        have := congrArg Prod.snd this; simp at this
      have hd := hm _ hzT _ hzT' hne
      apply Finset.disjoint_left.mp hd (rail_meet L z)
      simp [verts, rail]; omega
    · intro x hx hx0
      obtain ⟨hxr, hxT⟩ := hx0
      have hL : 0 < L := (Finset.mem_product.mp hxr).2 |> Finset.mem_range.mp
      obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
      have heT : lift L e ∈ T := by
        rw [← hS'] at he; exact (Finset.mem_filter.mp he).2
      have hne : lift L e ≠ rail L (x, 0) := lift_ne_rail (by simpa using hL)
      have hd := hm _ heT _ hxT hne
      have h1 : x * (L + 1) ∈ verts (lift L e) := by
        simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hxe
        simp only [verts, lift, Finset.mem_insert, Finset.mem_singleton]
        rcases hxe with rfl | rfl <;> simp
      have h2 : x * (L + 1) ∈ verts (rail L (x, 0)) := by simp [verts, rail]
      exact Finset.disjoint_left.mp hd h1 h2
  ·
    intro I hI
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset] at hI
    obtain ⟨hIs, hc, h0⟩ := hI
    have hIL : ∀ z ∈ I, z.2 < L := fun z hz => Finset.mem_range.mp (Finset.mem_product.mp (hIs hz)).2
    simp only [bigF, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨Finset.union_subset_union (Finset.image_subset_image hSE) (Finset.image_subset_image hIs), ?_⟩, ?_⟩
    · intro t1 ht1 t2 ht2 hne
      rcases Finset.mem_union.mp ht1 with h1 | h1 <;> rcases Finset.mem_union.mp ht2 with h2 | h2
      · obtain ⟨e1, he1, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨e2, he2, rfl⟩ := Finset.mem_image.mp h2
        exact lift_disj (hS e1 he1 e2 he2 (fun h => hne (h ▸ rfl)))
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h2
        by_contra h
        obtain ⟨hz0, hz1⟩ := lift_rail (hIL z hz) h
        apply h0 z.1 (Finset.mem_biUnion.mpr ⟨e, he, by rcases hz1 with h | h <;> simp [verts, h]⟩)
        have : z = (z.1, 0) := Prod.ext rfl hz0
        rw [← this]; exact hz
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h2
        by_contra h
        obtain ⟨hz0, hz1⟩ := lift_rail (hIL z hz) (fun hd => h hd.symm)
        apply h0 z.1 (Finset.mem_biUnion.mpr ⟨e, he, by rcases hz1 with h | h <;> simp [verts, h]⟩)
        have : z = (z.1, 0) := Prod.ext rfl hz0
        rw [← this]; exact hz
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h2
        by_contra h
        rcases rail_rail (hIL z hz) (hIL w hw) (fun e => hne (e ▸ rfl)) h with e | e
        · exact hc z hz (e ▸ hw)
        · exact hc w hw (e ▸ hz)
    · ext e
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨heE, ⟨e', he', hee⟩ | ⟨z, hz, hze⟩⟩
        · rw [← lift_inj hee]; exact he'
        · exact absurd hze.symm (lift_ne_rail (hIL z hz))
      · intro he; exact ⟨hSE he, Or.inl ⟨e, he, rfl⟩⟩
  ·
    intro T hT
    simp only [bigF, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨⟨hsub, hm⟩, hS'⟩ := hT
    ext t
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro (⟨e, he, rfl⟩ | ⟨z, ⟨_, hzT⟩, rfl⟩)
      · rw [← hS'] at he; exact (Finset.mem_filter.mp he).2
      · exact hzT
    · intro ht
      rcases Finset.mem_union.mp (hsub ht) with h | h
      · obtain ⟨e, heE, rfl⟩ := Finset.mem_image.mp h
        left; refine ⟨e, ?_, rfl⟩
        rw [← hS']; exact Finset.mem_filter.mpr ⟨heE, ht⟩
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
        right; exact ⟨z, ⟨hz, ht⟩, rfl⟩
  ·
    intro I hI
    simp only [Gset, Finset.mem_filter, Finset.mem_powerset] at hI
    have hIL : ∀ z ∈ I, z.2 < L := fun z hz => Finset.mem_range.mp (Finset.mem_product.mp (hI.1 hz)).2
    ext z
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hzr, ⟨e, _, he⟩ | ⟨w, hw, hwz⟩⟩
      · exact absurd he (lift_ne_rail (Finset.mem_range.mp (Finset.mem_product.mp hzr).2))
      · rw [← rail_inj (hIL w hw) (Finset.mem_range.mp (Finset.mem_product.mp hzr).2) hwz]; exact hw
    · intro hz; exact ⟨hI.1 hz, Or.inr ⟨z, hz, rfl⟩⟩

theorem cov_card (S : Finset (ℕ × ℕ)) (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) : (cov S).card = 2 * S.card := by
  unfold cov
  rw [Finset.card_biUnion (fun e he g hg hne => hS e he g hg hne)]
  rw [Finset.sum_congr rfl (g := fun _ => 2) (fun e he => by unfold verts; exact Finset.card_pair (Nat.ne_of_lt (hlt e he)))]
  simp [mul_comm]

theorem cov_sub (v : ℕ) (S : Finset (ℕ × ℕ)) (hv : ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v) : cov S ⊆ Finset.range v := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
  simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hxe
  have := hv e he
  exact Finset.mem_range.mpr (by rcases hxe with rfl | rfl <;> omega)

theorem part1 (v L : ℕ) (E S : Finset (ℕ × ℕ)) (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < v) (hSE : S ⊆ E) (hS : IsMatch S) :
    ((bigF v L E).filter (fun T => E.filter (fun e => lift L e ∈ T) = S)).card =
      Nat.fib (L + 1) ^ (2 * S.card) * Nat.fib (L + 2) ^ (v - 2 * S.card) := by
  rw [fiber_card v L E S hSE hS, Gset_card' v L (cov S) (cov_sub v S (fun e he => hE e (hSE he))),
    cov_card S hS (fun e he => (hE e (hSE he)).1)]

theorem restrict_mem (v L : ℕ) (E : Finset (ℕ × ℕ)) (T : Finset (ℕ × ℕ)) (hT : T ∈ bigF v L E) :
    E.filter (fun e => lift L e ∈ T) ∈ E.powerset.filter IsMatch := by
  simp only [bigF, Finset.mem_filter, Finset.mem_powerset] at hT
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  intro e he g hg hne
  obtain ⟨_, heT⟩ := Finset.mem_filter.mp he
  obtain ⟨_, hgT⟩ := Finset.mem_filter.mp hg
  exact lift_disj_rev (hT.2 _ heT _ hgT (fun h => hne (lift_inj h)))

theorem card_le_half (v : ℕ) (S : Finset (ℕ × ℕ)) (hS : IsMatch S) (hv : ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v) :
    S.card ≤ v / 2 := by
  have h1 := cov_card S hS (fun e he => (hv e he).1)
  have h2 := Finset.card_le_card (cov_sub v S hv)
  rw [Finset.card_range] at h2
  omega

theorem part2 (v L : ℕ) (E : Finset (ℕ × ℕ)) (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < v) :
    (bigF v L E).card = (Finset.range (v / 2 + 1)).sum (fun r =>
      ((E.powerset.filter IsMatch).filter (fun S => S.card = r)).card *
        Nat.fib (L + 1) ^ (2 * r) * Nat.fib (L + 2) ^ (v - 2 * r)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun T => E.filter (fun e => lift L e ∈ T))
    (t := E.powerset.filter IsMatch) (fun T hT => restrict_mem v L E T hT)]
  have hfib : ∀ S ∈ E.powerset.filter IsMatch,
      ((bigF v L E).filter (fun T => E.filter (fun e => lift L e ∈ T) = S)).card =
        Nat.fib (L + 1) ^ (2 * S.card) * Nat.fib (L + 2) ^ (v - 2 * S.card) := by
    intro S hS
    obtain ⟨hSE, hSm⟩ := Finset.mem_filter.mp hS
    exact part1 v L E S hE (Finset.mem_powerset.mp hSE) hSm
  rw [Finset.sum_congr rfl hfib]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (v / 2 + 1))]
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_congr rfl (g := fun _ => Nat.fib (L + 1) ^ (2 * r) * Nat.fib (L + 2) ^ (v - 2 * r))
      (fun S hS => by rw [(Finset.mem_filter.mp hS).2])]
    rw [Finset.sum_const, smul_eq_mul, mul_assoc]
  · intro S hS
    obtain ⟨hSE, hSm⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (card_le_half v S hSm (fun e he => hE e (Finset.mem_powerset.mp hSE he))))

def Pset (S : Finset (ℕ × ℕ)) (x : ℕ) : Finset ℕ :=
  (S.filter (fun e => e.1 = x)).image Prod.snd ∪ (S.filter (fun e => e.2 = x)).image Prod.fst

def partner (S : Finset (ℕ × ℕ)) (x : ℕ) : ℕ := if Pset S x = ∅ then x else (Pset S x).sum id

theorem share {S : Finset (ℕ × ℕ)} (hS : IsMatch S) {e e' : ℕ × ℕ} (he : e ∈ S) (he' : e' ∈ S) {x : ℕ}
    (hx : x ∈ verts e) (hx' : x ∈ verts e') : e = e' := by
  by_contra hne
  exact Finset.disjoint_left.mp (hS e he e' he' hne) hx hx'

theorem Pset_fst {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) {e : ℕ × ℕ} (he : e ∈ S) :
    Pset S e.1 = {e.2} := by
  ext y
  simp only [Pset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (⟨e', ⟨he', h1⟩, rfl⟩ | ⟨e', ⟨he', h2⟩, rfl⟩)
    · have := share hS he he' (x := e.1) (by simp [verts]) (by simp [verts, h1])
      rw [← this]
    · have := share hS he he' (x := e.1) (by simp [verts]) (by simp [verts, h2])
      subst this; have := hlt e he; omega
  · rintro rfl; exact Or.inl ⟨e, ⟨he, rfl⟩, rfl⟩

theorem Pset_snd {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) {e : ℕ × ℕ} (he : e ∈ S) :
    Pset S e.2 = {e.1} := by
  ext y
  simp only [Pset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (⟨e', ⟨he', h1⟩, rfl⟩ | ⟨e', ⟨he', h2⟩, rfl⟩)
    · have := share hS he he' (x := e.2) (by simp [verts]) (by simp [verts, h1])
      subst this; have := hlt e he; omega
    · have := share hS he he' (x := e.2) (by simp [verts]) (by simp [verts, h2])
      rw [← this]
  · rintro rfl; exact Or.inr ⟨e, ⟨he, rfl⟩, rfl⟩

theorem Pset_empty {S : Finset (ℕ × ℕ)} {x : ℕ} (hx : ∀ e ∈ S, x ∉ verts e) : Pset S x = ∅ := by
  ext y
  simp only [Pset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro (⟨e, ⟨he, h1⟩, rfl⟩ | ⟨e, ⟨he, h2⟩, rfl⟩)
  · exact hx e he (by simp [verts, h1])
  · exact hx e he (by simp [verts, h2])

theorem partner_fst {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) {e : ℕ × ℕ} (he : e ∈ S) :
    partner S e.1 = e.2 := by
  unfold partner; rw [Pset_fst hS hlt he]; simp

theorem partner_snd {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) {e : ℕ × ℕ} (he : e ∈ S) :
    partner S e.2 = e.1 := by
  unfold partner; rw [Pset_snd hS hlt he]; simp

theorem partner_free {S : Finset (ℕ × ℕ)} {x : ℕ} (hx : ∀ e ∈ S, x ∉ verts e) : partner S x = x := by
  unfold partner; rw [Pset_empty hx]; simp

theorem partner_invol {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) (x : ℕ) :
    partner S (partner S x) = x := by
  by_cases h : ∃ e ∈ S, x ∈ verts e
  · obtain ⟨e, he, hx⟩ := h
    simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [partner_fst hS hlt he, partner_snd hS hlt he]
    · rw [partner_snd hS hlt he, partner_fst hS hlt he]
  · push Not at h
    rw [partner_free h, partner_free h]

theorem partner_lt {v : ℕ} {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hv : ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v) {x : ℕ}
    (hx : x < v) : partner S x < v := by
  by_cases h : ∃ e ∈ S, x ∈ verts e
  · obtain ⟨e, he, hx'⟩ := h
    simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hx'
    have := hv e he
    rcases hx' with rfl | rfl
    · rw [partner_fst hS (fun e he => (hv e he).1) he]; exact this.2
    · rw [partner_snd hS (fun e he => (hv e he).1) he]; omega
  · push Not at h
    rw [partner_free h]; exact hx

theorem matchings_le_factorial (v : ℕ) (E : Finset (ℕ × ℕ)) (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < v) :
    (E.powerset.filter IsMatch).card ≤ v.factorial := by
  classical
  have key : ∀ S ∈ E.powerset.filter IsMatch, IsMatch S ∧ ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v := by
    intro S hS
    obtain ⟨hSE, hSm⟩ := Finset.mem_filter.mp hS
    exact ⟨hSm, fun e he => hE e (Finset.mem_powerset.mp hSE he)⟩
  let f : (ℕ × ℕ) → ℕ → ℕ := fun _ x => x
  let σ : Finset (ℕ × ℕ) → (Fin v → Fin v) := fun S i =>
    if h : IsMatch S ∧ ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v then ⟨partner S i, partner_lt h.1 h.2 i.2⟩ else i
  have hσ : ∀ S ∈ E.powerset.filter IsMatch, Function.Involutive (σ S) := by
    intro S hS i
    have h := key S hS
    simp only [σ, dif_pos h]
    exact Fin.ext (partner_invol h.1 (fun e he => (h.2 e he).1) i)
  let F : Finset (ℕ × ℕ) → Equiv.Perm (Fin v) := fun S =>
    if h : S ∈ E.powerset.filter IsMatch then Function.Involutive.toPerm (σ S) (hσ S h) else 1
  have ev : ∀ S ∈ E.powerset.filter IsMatch, ∀ i : Fin v, ((F S i : Fin v) : ℕ) = partner S i := by
    intro S hS i
    have h := key S hS
    simp only [F, dif_pos hS, Function.Involutive.coe_toPerm, σ, dif_pos h]
  calc (E.powerset.filter IsMatch).card
      ≤ (Finset.univ : Finset (Equiv.Perm (Fin v))).card := by
        refine Finset.card_le_card_of_injOn F (fun _ _ => Finset.mem_univ _) ?_
        intro S hS S' hS' heq
        have h := key S hS
        have h' := key S' hS'
        have hp : ∀ x, x < v → partner S x = partner S' x := by
          intro x hx
          have := congrArg (fun p : Equiv.Perm (Fin v) => ((p ⟨x, hx⟩ : Fin v) : ℕ)) heq
          rwa [ev S hS, ev S' hS'] at this
        have sub : ∀ (A B : Finset (ℕ × ℕ)), IsMatch A → (∀ e ∈ A, e.1 < e.2 ∧ e.2 < v) → IsMatch B →
            (∀ e ∈ B, e.1 < e.2 ∧ e.2 < v) → (∀ x, x < v → partner A x = partner B x) → A ⊆ B := by
          intro A B hA hAv hB hBv hAB e he
          have h1 := partner_fst hA (fun e he => (hAv e he).1) he
          rw [hAB e.1 (by have := hAv e he; omega)] at h1
          by_cases hc : ∃ g ∈ B, e.1 ∈ verts g
          · obtain ⟨g, hg, hxg⟩ := hc
            simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hxg
            have hgv := hBv g hg
            rcases hxg with h0 | h0
            · rw [h0, partner_fst hB (fun e he => (hBv e he).1) hg] at h1
              have : g = e := Prod.ext h0.symm h1
              rw [← this]; exact hg
            · rw [h0, partner_snd hB (fun e he => (hBv e he).1) hg] at h1
              have := hAv e he; omega
          · push Not at hc
            rw [partner_free hc] at h1
            have := hAv e he; omega
        exact Finset.Subset.antisymm (sub S S' h.1 h.2 h'.1 h'.2 hp)
          (sub S' S h'.1 h'.2 h.1 h.2 (fun x hx => (hp x hx).symm))
    _ = v.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

def Q (m : ℕ → ℕ) (a b n : ℕ) : ℕ := (Finset.range (n + 1)).sum (fun r => m r * a ^ (2 * r) * b ^ (2 * (n - r)))

theorem Q_succ (m : ℕ → ℕ) (a b n : ℕ) : Q m a b (n + 1) = Q m a b n * b ^ 2 + m (n + 1) * a ^ (2 * (n + 1)) := by
  unfold Q
  rw [Finset.sum_range_succ, Nat.sub_self, Nat.mul_zero, pow_zero, Nat.mul_one, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  rw [show 2 * (n + 1 - r) = 2 * (n - r) + 2 by omega, pow_add]; ring

theorem pow_mod_one {a b : ℕ} (ha : a ^ 2 % b = 1) (hb : 1 < b) (n : ℕ) : a ^ (2 * n) % b = 1 := by
  rw [pow_mul, Nat.pow_mod, ha, one_pow, Nat.one_mod_eq_one.mpr (by omega)]

theorem Q_mod (m : ℕ → ℕ) {a b : ℕ} (ha : a ^ 2 % b = 1) (hb : 1 < b) (n : ℕ) (hm : m n < b) :
    Q m a b n % b = m n := by
  cases n with
  | zero => simp [Q, Nat.mod_eq_of_lt hm]
  | succ n =>
    rw [Q_succ, Nat.add_mod, show Q m a b n * b ^ 2 = (Q m a b n * b) * b by ring, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_mod, Nat.mul_mod, pow_mod_one ha hb, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hm]

theorem rounds (m : ℕ → ℕ) {a b d : ℕ} (ha : a ^ 2 % b = 1) (hb : 1 < b) (hm : ∀ r ≤ d, m r < b) (z0 : ℕ)
    (hz0 : z0 = Q m a b d) :
    ∀ k, k ≤ d → (Nat.rec (motive := fun _ => ℕ) z0
      (fun roundIndex z => (z - (z % b) * a ^ (2 * (d - roundIndex))) / b ^ 2) k : ℕ) = Q m a b (d - k) := by
  intro k
  induction k with
  | zero => intro _; simpa using hz0
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    simp only at ih' ⊢
    rw [ih']
    obtain ⟨n, hn⟩ : ∃ n, d - k = n + 1 := ⟨d - k - 1, by omega⟩
    rw [hn, Q_mod m ha hb (n + 1) (hm _ (by omega)), Q_succ, Nat.add_sub_cancel,
      Nat.mul_div_cancel _ (by positivity), show d - (k + 1) = n by omega]

theorem big_eq (m : ℕ → ℕ) (a b v : ℕ) :
    (Finset.range (v / 2 + 1)).sum (fun r => m r * a ^ (2 * r) * b ^ (v - 2 * r)) = b ^ (v % 2) * Q m a b (v / 2) := by
  unfold Q
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  rw [show v - 2 * r = v % 2 + 2 * (v / 2 - r) by omega, pow_add]; ring

end PEqualNP.Outside.L_meta_32063.L924


namespace PEqualNP.Outside.L_meta_32063.Bridge

open PEqualNP.Outside.L_meta_32063.L853
open PEqualNP.Outside.L_meta_32063.L924

theorem fib_gt_two_pow : ∀ m : ℕ, 2 ^ m < Nat.fib (2 * m + 4)
  | 0 => by decide
  | m + 1 => by
    have ih := fib_gt_two_pow m
    have h1 : Nat.fib (2 * (m + 1) + 4) = Nat.fib (2 * m + 4) + Nat.fib (2 * m + 5) :=
      Nat.fib_add_two
    have h2 : Nat.fib (2 * m + 5) = Nat.fib (2 * m + 3) + Nat.fib (2 * m + 4) :=
      Nat.fib_add_two
    have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
    omega

theorem fact_le_pow : ∀ v : ℕ, v.factorial ≤ v ^ v
  | 0 => by decide
  | v + 1 => by
    have ih := fact_le_pow v
    calc (v + 1).factorial = (v + 1) * v.factorial := Nat.factorial_succ v
      _ ≤ (v + 1) * v ^ v := Nat.mul_le_mul_left _ ih
      _ ≤ (v + 1) * (v + 1) ^ v := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ v) v)
      _ = (v + 1) ^ (v + 1) := (pow_succ' (v + 1) v).symm

theorem fact_lt_fib_L (n : ℕ) :
    let v := 2 * n
    let L := 2 * (1 + v * ((v + 1).log2 + 1))
    v.factorial < Nat.fib (L + 2) := by
  intro v L
  let t := (v + 1).log2 + 1
  have hv : v < 2 ^ t := by
    have hlt : v + 1 < 2 ^ (Nat.log 2 (v + 1)).succ :=
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) (v + 1)
    rw [← Nat.log2_eq_log_two] at hlt
    exact Nat.lt_of_succ_lt hlt
  have h1 : v.factorial ≤ 2 ^ (v * t) := by
    calc v.factorial ≤ v ^ v := fact_le_pow v
      _ ≤ (2 ^ t) ^ v := Nat.pow_le_pow_left (Nat.le_of_lt hv) v
      _ = 2 ^ (t * v) := (pow_mul 2 t v).symm
      _ = 2 ^ (v * t) := by rw [Nat.mul_comm]
  have h2 : 2 ^ (v * t) < Nat.fib (2 * (v * t) + 4) := fib_gt_two_pow (v * t)
  have hL : L + 2 = 2 * (v * t) + 4 := by
    show 2 * (1 + v * t) + 2 = 2 * (v * t) + 4
    omega
  rw [hL]
  exact Nat.lt_of_le_of_lt h1 h2

theorem invFn_id (k : ℕ) (x y : Fin k → Bool) :
    decide (∃ i : Fin k,
      (x i = true ∧ y i = true) ∨
      ((1 : Equiv.Perm (Fin k)) i ≠ i ∧
        ((x i = true ∧ x ((1 : Equiv.Perm (Fin k)) i) = true) ∨
         (y i = true ∧ y ((1 : Equiv.Perm (Fin k)) i) = true)))) =
    decide (∃ i : Fin k, x i = true ∧ y i = true) := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem fits_identity (n : ℕ) (hn : 0 < n) (ban : List (ℕ × ℕ)) :
    let v := 2 * n
    let L := 2 * (1 + v * ((v + 1).log2 + 1))
    let k := v * (L + 1)
    let Fn := (Fin k → Bool) → (Fin k → Bool) → Bool
    let f0 : Fn := fun x y => decide (∃ i, x i = true ∧ y i = true)
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2 * k ∧
      PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
      ∀ x y, f0 x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
    ∀ e ∈ ban, f0 (fun i => decide (i.val = e.1 ∨ i.val = e.2)) (fun _ => false) = false := by
  intro v L k Fn f0
  have hk0 : 0 < k := by
    have hv : 0 < v := by omega
    have hL : 0 < L + 1 := by omega
    exact Nat.mul_pos hv hL
  constructor
  · obtain ⟨C, hm, hs, hr, he⟩ := L853.R019.InverseBridge.involution_circuit_of_compiler
      (fun h => L853.R020.ROCompiler.ro_circuit_exists h) hk0 (1 : Equiv.Perm (Fin k)) (fun _ => rfl)
    refine ⟨C, hm, hs, hr, fun x y => ?_⟩
    rw [he x y]
    exact (invFn_id k x y).symm
  · intro e _
    simp [f0]

def invFunOf {k : ℕ} (p : Equiv.Perm (Fin k)) : (Fin k → Bool) → (Fin k → Bool) → Bool :=
  fun x y => decide (∃ i : Fin k,
    (x i = true ∧ y i = true) ∨
    (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨ (y i = true ∧ y (p i) = true))))

theorem invFunOf_probe {k : ℕ} (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (a b : ℕ) (ha : a < k) (hb : b < k) (hab : a < b) :
    invFunOf p (fun i => decide (i.val = a ∨ i.val = b)) (fun _ => false) = true ↔
      p ⟨a, ha⟩ = ⟨b, hb⟩ := by
  simp only [invFunOf, decide_eq_true_eq, Bool.false_eq_true, and_false, or_false, false_or]
  constructor
  · rintro ⟨i, hne, hi, hpi⟩
    rcases hi with hia | hib
    · have hi' : i = ⟨a, ha⟩ := Fin.ext hia
      subst hi'
      rcases hpi with h1 | h2
      · exact absurd (Fin.ext h1) hne
      · exact Fin.ext h2
    · have hi' : i = ⟨b, hb⟩ := Fin.ext hib
      subst hi'
      rcases hpi with h1 | h2
      · have hpa : p ⟨b, hb⟩ = ⟨a, ha⟩ := Fin.ext h1
        have := congrArg p hpa
        rw [hp ⟨b, hb⟩] at this
        exact this.symm
      · exact absurd (Fin.ext h2) hne
  · intro h
    refine ⟨⟨a, ha⟩, ?_, Or.inl rfl, Or.inr ?_⟩
    · intro heq; rw [h] at heq; have := congrArg Fin.val heq; dsimp only at this; omega
    · rw [h]

theorem invFunOf_inj {k : ℕ} (hk : 2 ≤ k) {p q : Equiv.Perm (Fin k)}
    (hp : Function.Involutive p) (hq : Function.Involutive q)
    (heq : invFunOf p = invFunOf q) : p = q := by
  have hk0 : 0 < k := by omega
  obtain ⟨C, hm, hs, hr, he⟩ := L853.R019.InverseBridge.involution_circuit_of_compiler
    (fun h => L853.R020.ROCompiler.ro_circuit_exists h) hk0 p hp
  have hiff := (L853.R019.official_full k hk (invFunOf p)).mp
    ⟨C, hm, hs, hr, fun x y => (he x y).symm⟩
  obtain ⟨r, -, huniq⟩ := hiff
  have hp1 : p = r := huniq p ⟨hp, fun _ _ => rfl⟩
  have hq1 : q = r := huniq q ⟨hq, fun x y => congrFun (congrFun heq x) y⟩
  exact hp1.trans hq1.symm

def edgeSet {n : ℕ} (A : Fin n → Fin n → Bool) : Finset (ℕ × ℕ) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => A z.1 z.2 = true)).image
    (fun z => (z.1.val, n + z.2.val))

theorem edgeSet_lt {n : ℕ} (A : Fin n → Fin n → Bool) :
    ∀ e ∈ edgeSet A, e.1 < e.2 ∧ e.2 < 2 * n := by
  intro e he
  simp only [edgeSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rcases he with ⟨z, -, rfl⟩
  omega

theorem mem_base_iff_mem_lift {n L : ℕ} (A : Fin n → Fin n → Bool) (x y : ℕ) :
    let cells := (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))
    let base := (cells.filter (fun z => A z.1 z.2)).map (fun z =>
      (z.1.val * (L + 1), (n + z.2.val) * (L + 1)))
    (x, y) ∈ base ↔ (x, y) ∈ (edgeSet A).image (L924.lift L) := by
  intro cells base
  simp only [base, cells, edgeSet, L924.lift, List.mem_map, List.mem_filter,
    List.mem_flatMap, List.mem_finRange, true_and, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨⟨i', j', h1⟩, hA⟩, h2⟩
    rcases Prod.mk.inj h1 with ⟨rfl, rfl⟩
    exact ⟨(i'.val, n + j'.val), ⟨(i', j'), hA, rfl⟩, h2⟩
  · rintro ⟨e, ⟨⟨i, j⟩, hA, rfl⟩, h2⟩
    exact ⟨(i, j), ⟨⟨i, j, rfl⟩, hA⟩, h2⟩

theorem rail_iff_mem_rails {v L x y : ℕ} (hx : x < v * (L + 1)) :
    (y = x + 1 ∧ x / (L + 1) = y / (L + 1)) ↔ (x, y) ∈ L924.railsF v L := by
  simp only [L924.railsF, L924.rail, Finset.mem_image, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨rfl, hdiv⟩
    refine ⟨(x / (L + 1), x % (L + 1)), ⟨?_, ?_⟩, ?_⟩
    · exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    · have hmod : x % (L + 1) < L + 1 := Nat.mod_lt x (Nat.succ_pos L)
      by_contra hge
      have hrem : x % (L + 1) = L := by dsimp only at hge; omega
      have hxeq : x = (L + 1) * (x / (L + 1)) + L := by
        have := Nat.div_add_mod x (L + 1); omega
      have hx1 : x + 1 = (x / (L + 1) + 1) * (L + 1) := by
        have h1 : (x / (L + 1) + 1) * (L + 1) = (L + 1) * (x / (L + 1)) + (L + 1) := by ring
        omega
      rw [hx1, Nat.mul_div_cancel _ (Nat.succ_pos L)] at hdiv
      omega
    · have := Nat.div_add_mod x (L + 1)
      have hm : x / (L + 1) * (L + 1) + x % (L + 1) = x := by
        rw [Nat.mul_comm]; exact this
      exact Prod.ext hm (by rw [hm])
  · rintro ⟨⟨q, r⟩, ⟨hq, hr⟩, hxy⟩
    rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    have h1 : (q * (L + 1) + r) / (L + 1) = q := by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (Nat.succ_pos L),
          Nat.div_eq_of_lt (by omega : r < L + 1), Nat.zero_add]
    have h2 : (q * (L + 1) + r + 1) / (L + 1) = q := by
      rw [show q * (L + 1) + r + 1 = (r + 1) + (L + 1) * q by ring,
          Nat.add_mul_div_left _ _ (Nat.succ_pos L),
          Nat.div_eq_of_lt (by omega : r + 1 < L + 1), Nat.zero_add]
    rw [h1, h2]

theorem good_iff_mem_bigEdges {n : ℕ} (A : Fin n → Fin n → Bool) (x y : ℕ) :
    let v := 2 * n
    let L := 2 * (1 + v * ((v + 1).log2 + 1))
    let k := v * (L + 1)
    let cells := (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))
    let base := (cells.filter (fun z => A z.1 z.2)).map (fun z =>
      (z.1.val * (L + 1), (n + z.2.val) * (L + 1)))
    let good := fun (x y : ℕ) => (x, y) ∈ base ∨ (y = x + 1 ∧ x / (L + 1) = y / (L + 1))
    x < k → (good x y ↔ (x, y) ∈ (edgeSet A).image (L924.lift L) ∪ L924.railsF v L) := by
  intro v L k cells base good hx
  rw [Finset.mem_union]
  exact or_congr (mem_base_iff_mem_lift A x y) (rail_iff_mem_rails hx)

theorem bigEdges_lt {n : ℕ} (A : Fin n → Fin n → Bool) :
    let v := 2 * n
    let L := 2 * (1 + v * ((v + 1).log2 + 1))
    let k := v * (L + 1)
    ∀ e ∈ (edgeSet A).image (L924.lift L) ∪ L924.railsF v L, e.1 < e.2 ∧ e.2 < k := by
  intro v L k e he
  rcases Finset.mem_union.mp he with h1 | h2
  · rcases Finset.mem_image.mp h1 with ⟨g, hg, rfl⟩
    have hlt := edgeSet_lt A g hg
    simp only [L924.lift]
    refine ⟨Nat.mul_lt_mul_of_pos_right hlt.1 (Nat.succ_pos L),
      Nat.mul_lt_mul_of_pos_right hlt.2 (Nat.succ_pos L)⟩
  · rcases Finset.mem_image.mp h2 with ⟨⟨q, r⟩, hqr, rfl⟩
    simp only [Finset.mem_product, Finset.mem_range] at hqr
    simp only [L924.rail]
    refine ⟨by omega, ?_⟩
    have hq1 : q + 1 ≤ v := hqr.1
    have hmul : (q + 1) * (L + 1) ≤ v * (L + 1) := Nat.mul_le_mul_right _ hq1
    have hexp : (q + 1) * (L + 1) = q * (L + 1) + (L + 1) := by ring
    omega

theorem Z_eq_big_card_aux (k : ℕ) (hk2 : 2 ≤ k) (G : Finset (ℕ × ℕ))
    (hGlt : ∀ e ∈ G, e.1 < e.2 ∧ e.2 < k) (ban : List (ℕ × ℕ))
    (hban : ∀ e : ℕ × ℕ, e ∈ ban ↔ e.1 < e.2 ∧ e.2 < k ∧ e ∉ G) :
    let Fn := (Fin k → Bool) → (Fin k → Bool) → Bool
    let fits := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2 * k ∧
      PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
      ∀ e ∈ ban, f (fun i => decide (i.val = e.1 ∨ i.val = e.2)) (fun _ => false) = false
    Nat.card {f : Fn // fits f} = (G.powerset.filter L924.IsMatch).card := by
  classical
  intro Fn fits
  have hk0 : 0 < k := by omega
  let big := G.powerset.filter L924.IsMatch
  have hbig_mem : ∀ T, T ∈ big ↔ T ⊆ G ∧ L924.IsMatch T := by
    intro T; simp [big]
  have hbig_lt : ∀ T ∈ big, ∀ e ∈ T, e.1 < e.2 ∧ e.2 < k := fun T hT e he =>
    hGlt e (((hbig_mem T).mp hT).1 he)
  let toPermFun : Finset (ℕ × ℕ) → Fin k → Fin k := fun T i =>
    if h : T ∈ big then
      ⟨L924.partner T i.val, L924.partner_lt ((hbig_mem T).mp h).2 (hbig_lt T h) i.isLt⟩
    else i
  have htoPermInvol : ∀ T, Function.Involutive (toPermFun T) := by
    intro T i
    by_cases h : T ∈ big
    · simp only [toPermFun, h, ↓reduceDIte]
      exact Fin.ext (L924.partner_invol ((hbig_mem T).mp h).2
        (fun e he => (hbig_lt T h e he).1) i.val)
    · simp [toPermFun, h]
  let toPerm : Finset (ℕ × ℕ) → Equiv.Perm (Fin k) := fun T =>
    Function.Involutive.toPerm (toPermFun T) (htoPermInvol T)
  have htoPerm_val : ∀ T ∈ big, ∀ i : Fin k, (toPerm T i).val = L924.partner T i.val := by
    intro T hT i
    simp [toPerm, toPermFun, hT]
  let toFn : Finset (ℕ × ℕ) → Fn := fun T => invFunOf (toPerm T)
  have htoFn_fits : ∀ T ∈ big, fits (toFn T) := by
    intro T hT
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hm, hs, hr, he⟩ := L853.R019.InverseBridge.involution_circuit_of_compiler
        (fun h => L853.R020.ROCompiler.ro_circuit_exists h) hk0 (toPerm T) (htoPermInvol T)
      exact ⟨C, hm, hs, hr, fun x y => (he x y).symm⟩
    · intro e he
      obtain ⟨h12, h2k, hneG⟩ := (hban e).mp he
      have h1k : e.1 < k := by omega
      cases hval : toFn T (fun i => decide (i.val = e.1 ∨ i.val = e.2)) (fun _ => false)
      · rfl
      · exfalso
        have hp := (invFunOf_probe (toPerm T) (htoPermInvol T) e.1 e.2 h1k h2k h12).mp hval
        have hpart : L924.partner T e.1 = e.2 := by
          have := congrArg Fin.val hp
          rwa [htoPerm_val T hT ⟨e.1, h1k⟩] at this
        by_cases hinc : ∃ g ∈ T, e.1 ∈ L924.verts g
        · obtain ⟨g, hg, hxg⟩ := hinc
          simp only [L924.verts, Finset.mem_insert, Finset.mem_singleton] at hxg
          rcases hxg with h0 | h0
          · have hpf := L924.partner_fst ((hbig_mem T).mp hT).2
              (fun g' hg' => (hbig_lt T hT g' hg').1) hg
            rw [← h0, hpart] at hpf
            have hge : g = e := Prod.ext h0.symm hpf.symm
            rw [← hge] at hneG
            exact hneG (((hbig_mem T).mp hT).1 hg)
          · have hps := L924.partner_snd ((hbig_mem T).mp hT).2
              (fun g' hg' => (hbig_lt T hT g' hg').1) hg
            rw [← h0, hpart] at hps
            have hglt := (hbig_lt T hT g hg).1
            omega
        · push_neg at hinc
          rw [L924.partner_free hinc] at hpart
          omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  symm
  refine Finset.card_bij (fun T _ => toFn T) ?_ ?_ ?_
  · intro T hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htoFn_fits T hT⟩
  · intro T1 hT1 T2 hT2 heq
    have hp : toPerm T1 = toPerm T2 := invFunOf_inj hk2 (htoPermInvol T1) (htoPermInvol T2) heq
    have hpart : ∀ x < k, L924.partner T1 x = L924.partner T2 x := by
      intro x hx
      have := congrArg (fun p : Equiv.Perm (Fin k) => (p ⟨x, hx⟩).val) hp
      rwa [htoPerm_val T1 hT1 ⟨x, hx⟩, htoPerm_val T2 hT2 ⟨x, hx⟩] at this
    have sub : ∀ A1 A2, A1 ∈ big → A2 ∈ big → (∀ x < k, L924.partner A1 x = L924.partner A2 x) →
        A1 ⊆ A2 := by
      intro A1 A2 hA1 hA2 hAB e he
      have hlt1 := hbig_lt A1 hA1 e he
      have h1 := L924.partner_fst ((hbig_mem A1).mp hA1).2 (fun g hg => (hbig_lt A1 hA1 g hg).1) he
      rw [hAB e.1 (by omega)] at h1
      by_cases hc : ∃ g ∈ A2, e.1 ∈ L924.verts g
      · obtain ⟨g, hg, hxg⟩ := hc
        simp only [L924.verts, Finset.mem_insert, Finset.mem_singleton] at hxg
        rcases hxg with h0 | h0
        · rw [h0, L924.partner_fst ((hbig_mem A2).mp hA2).2
            (fun g' hg' => (hbig_lt A2 hA2 g' hg').1) hg] at h1
          have : g = e := Prod.ext h0.symm h1
          rwa [← this]
        · rw [h0, L924.partner_snd ((hbig_mem A2).mp hA2).2
            (fun g' hg' => (hbig_lt A2 hA2 g' hg').1) hg] at h1
          have := (hbig_lt A2 hA2 g hg).1
          omega
      · push_neg at hc
        rw [L924.partner_free hc] at h1
        omega
    exact Finset.Subset.antisymm (sub T1 T2 hT1 hT2 hpart)
      (sub T2 T1 hT2 hT1 (fun x hx => (hpart x hx).symm))
  · intro f hf
    have hfits : fits f := (Finset.mem_filter.mp hf).2
    obtain ⟨p, ⟨hp, hfp⟩, -⟩ := (L853.R019.official_full k hk2 f).mp hfits.1
    have hfeq : f = invFunOf p := by funext x y; exact hfp x y
    let T : Finset (ℕ × ℕ) :=
      (Finset.univ.filter (fun i : Fin k => i.val < (p i).val)).image (fun i => (i.val, (p i).val))
    have hTG : T ⊆ G := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
      have hlt : i.val < (p i).val := (Finset.mem_filter.mp hi).2
      by_contra hng
      have hmem : (i.val, (p i).val) ∈ ban := (hban _).mpr ⟨hlt, (p i).isLt, hng⟩
      have hprobe := hfits.2 _ hmem
      rw [hfeq] at hprobe
      have htrue := (invFunOf_probe p hp i.val (p i).val i.isLt (p i).isLt hlt).mpr rfl
      rw [hprobe] at htrue
      exact Bool.false_ne_true htrue
    have hTm : L924.IsMatch T := by
      intro e he g hg hne
      rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
      rcases Finset.mem_image.mp hg with ⟨j, hj, rfl⟩
      have hilt : i.val < (p i).val := (Finset.mem_filter.mp hi).2
      have hjlt : j.val < (p j).val := (Finset.mem_filter.mp hj).2
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [L924.verts, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      have hij : i ≠ j := fun h => hne (by subst h; rfl)
      rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
      · exact hij (Fin.ext h)
      · have h1 : i = p j := Fin.ext h
        have h2 : p i = j := by rw [h1, hp j]
        have := congrArg Fin.val h1; have := congrArg Fin.val h2; omega
      · have h1 : p i = j := Fin.ext h
        have h2 : i = p j := by rw [← h1, hp i]
        have := congrArg Fin.val h1; have := congrArg Fin.val h2; omega
      · exact hij (p.injective (Fin.ext h))
    have hTbig : T ∈ big := (hbig_mem T).mpr ⟨hTG, hTm⟩
    refine ⟨T, hTbig, ?_⟩
    rw [hfeq]
    have hpT : toPerm T = p := by
      ext i
      rw [htoPerm_val T hTbig i]
      by_cases hlt : i.val < (p i).val
      · have hiT : (i.val, (p i).val) ∈ T :=
          Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
        exact L924.partner_fst hTm (fun g hg => (hbig_lt T hTbig g hg).1) hiT
      · by_cases hgt : (p i).val < i.val
        · have hjT : ((p i).val, i.val) ∈ T := by
            refine Finset.mem_image.mpr ⟨p i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [hp i]; exact hgt
            · rw [hp i]
          exact L924.partner_snd hTm (fun g hg => (hbig_lt T hTbig g hg).1) hjT
        · have hpi : p i = i := Fin.ext (by omega)
          have hfree : ∀ g ∈ T, i.val ∉ L924.verts g := by
            intro g hg hmem
            rcases Finset.mem_image.mp hg with ⟨j, hj, rfl⟩
            have hjlt : j.val < (p j).val := (Finset.mem_filter.mp hj).2
            simp only [L924.verts, Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h | h
            · have : i = j := Fin.ext h; subst this; rw [hpi] at hjlt; omega
            · have : i = p j := Fin.ext h
              have : p i = j := by rw [this, hp j]
              rw [hpi] at this; subst this; rw [hpi] at hjlt; omega
          rw [L924.partner_free hfree, hpi]
    simp [toFn, hpT]

theorem Z_eq_big_card (n : ℕ) (hn : 0 < n) (A : Fin n → Fin n → Bool) :
    let v := 2 * n
    let L := 2 * (1 + v * ((v + 1).log2 + 1))
    let k := v * (L + 1)
    let cells := (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))
    let base := (cells.filter (fun z => A z.1 z.2)).map (fun z =>
      (z.1.val * (L + 1), (n + z.2.val) * (L + 1)))
    let good := fun (x y : Nat) => (x, y) ∈ base ∨ (y = x + 1 ∧ x / (L + 1) = y / (L + 1))
    let ban := (List.range k).flatMap (fun x => ((List.range k).filter (fun y =>
      decide (x < y ∧ ¬ good x y))).map (fun y => (x, y)))
    let Fn := (Fin k → Bool) → (Fin k → Bool) → Bool
    let fits := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2 * k ∧
      PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
      ∀ e ∈ ban, f (fun i => decide (i.val = e.1 ∨ i.val = e.2)) (fun _ => false) = false
    Nat.card {f : Fn // fits f} = (L924.bigF v L (edgeSet A)).card := by
  intro v L k cells base good ban Fn fits
  have hk2 : 2 ≤ k := by
    have hv : 2 ≤ v := by omega
    have hL : 1 ≤ L + 1 := by omega
    exact le_trans (by omega : 2 ≤ 2 * 1) (Nat.mul_le_mul hv hL)
  let G := (edgeSet A).image (L924.lift L) ∪ L924.railsF v L
  have hban : ∀ e : ℕ × ℕ, e ∈ ban ↔ e.1 < e.2 ∧ e.2 < k ∧ e ∉ G := by
    intro ⟨a, b⟩
    simp only [ban, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, y, ⟨hy, hxy, hng⟩, heq⟩
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      refine ⟨hxy, hy, ?_⟩
      intro hmem
      exact hng ((good_iff_mem_bigEdges A x y hx).mpr hmem)
    · rintro ⟨hab, hb, hng⟩
      have ha : a < k := by omega
      refine ⟨a, ha, b, ⟨hb, hab, ?_⟩, rfl⟩
      intro hgood
      exact hng ((good_iff_mem_bigEdges A a b ha).mp hgood)
  exact Z_eq_big_card_aux k hk2 G (bigEdges_lt A) ban hban

theorem m_n_eq_permanent (n : ℕ) (A : Fin n → Fin n → Bool) :
    let E := edgeSet A
    let old := E.powerset.filter L924.IsMatch
    let B : Matrix (Fin n) (Fin n) ℕ := fun i j => (A i j).toNat
    (old.filter (fun S => S.card = n)).card = B.permanent := by
  classical
  intro E old B
  have hperm : B.permanent =
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => ∀ i, A i (σ i) = true)).card := by
    have hdef : B.permanent = ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, B (σ i) i := rfl
    rw [hdef, Finset.card_filter]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    have hprod : (∏ i : Fin n, B (σ i) i) = ∏ i : Fin n, B i (σ⁻¹ i) := by
      refine Fintype.prod_equiv σ _ _ fun i => ?_
      simp [Equiv.symm_apply_apply]
    rw [hprod]
    change (∏ i : Fin n, B i (σ⁻¹ i)) = if ∀ i, A i (σ⁻¹ i) = true then 1 else 0
    by_cases h : ∀ i, A i (σ⁻¹ i) = true
    · rw [if_pos h]
      refine Finset.prod_eq_one fun i _ => ?_
      change (A i (σ⁻¹ i)).toNat = 1
      rw [h i]; rfl
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      have hAf : A i (σ⁻¹ i) = false := Bool.eq_false_iff.mpr hi
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      change (A i (σ⁻¹ i)).toNat = 0
      rw [hAf]; rfl
  rw [hperm]
  symm
  let Φ : Equiv.Perm (Fin n) → Finset (ℕ × ℕ) :=
    fun σ => Finset.univ.image (fun i : Fin n => (i.val, n + (σ i).val))
  refine Finset.card_bij (fun σ _ => Φ σ) ?_ ?_ ?_
  · intro σ hσ
    have hA := (Finset.mem_filter.mp hσ).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩, ?_⟩
    · intro e he
      rcases Finset.mem_image.mp he with ⟨i, -, rfl⟩
      exact Finset.mem_image.mpr ⟨(i, σ i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA i⟩, rfl⟩
    · intro e he g hg hne
      rcases Finset.mem_image.mp he with ⟨i, -, rfl⟩
      rcases Finset.mem_image.mp hg with ⟨j, -, rfl⟩
      have hij : i ≠ j := fun h => hne (by subst h; rfl)
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [L924.verts, Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      rcases hx1 with rfl | rfl <;> rcases hx2 with h | h
      · exact hij (Fin.ext h)
      · omega
      · omega
      · exact hij (σ.injective (Fin.ext (by omega)))
    · rw [Finset.card_image_of_injective _ (fun i j h => Fin.ext (Prod.mk.inj h).1),
          Finset.card_univ, Fintype.card_fin]
  · intro σ1 _ σ2 _ heq
    ext i
    have hmem : (i.val, n + (σ1 i).val) ∈ Φ σ2 := by
      rw [← heq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rcases Finset.mem_image.mp hmem with ⟨j, -, hj⟩
    rcases Prod.mk.inj hj with ⟨h1, h2⟩
    have hji : j = i := Fin.ext h1
    subst hji
    omega
  · intro S hS
    obtain ⟨hSold, hScard⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSE, hSm⟩ := Finset.mem_filter.mp hSold
    have hSE' : S ⊆ E := Finset.mem_powerset.mp hSE
    have hSlt : ∀ e ∈ S, e.1 < n ∧ n ≤ e.2 ∧ e.2 < 2 * n ∧
        ∃ (h1 : e.1 < n) (h2 : e.2 - n < n), A ⟨e.1, h1⟩ ⟨e.2 - n, h2⟩ = true := by
      intro e he
      rcases Finset.mem_image.mp (hSE' he) with ⟨⟨i, j⟩, hij, rfl⟩
      have hAij := (Finset.mem_filter.mp hij).2
      refine ⟨i.isLt, by omega, by omega, i.isLt, by omega, ?_⟩
      simpa [Nat.add_sub_cancel_left] using hAij
    have hfst_inj : Set.InjOn Prod.fst (S : Set (ℕ × ℕ)) := by
      intro e he g hg hfg
      by_contra hne
      exact Finset.disjoint_left.mp (hSm e he g hg hne)
        (Finset.mem_insert_self e.1 {e.2})
        (by rw [hfg]; exact Finset.mem_insert_self g.1 {g.2})
    have hfst_sub : S.image Prod.fst ⊆ Finset.range n := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
      exact Finset.mem_range.mpr (hSlt e he).1
    have hfst_eq : S.image Prod.fst = Finset.range n := by
      refine Finset.eq_of_subset_of_card_le hfst_sub ?_
      rw [Finset.card_image_of_injOn hfst_inj, hScard, Finset.card_range]
    have hEx : ∀ i : Fin n, ∃ e ∈ S, e.1 = i.val := by
      intro i
      have : i.val ∈ S.image Prod.fst := by rw [hfst_eq]; exact Finset.mem_range.mpr i.isLt
      rcases Finset.mem_image.mp this with ⟨e, he, h1⟩
      exact ⟨e, he, h1⟩
    have hpart_spec : ∀ i : Fin n, (i.val, L924.partner S i.val) ∈ S := by
      intro i
      obtain ⟨e, he, h1⟩ := hEx i
      have hpf := L924.partner_fst hSm (fun g hg => by have := hSlt g hg; omega) he
      rw [h1] at hpf
      rw [hpf]
      have : e = (i.val, e.2) := Prod.ext h1 rfl
      rwa [← this]
    let f : Fin n → Fin n := fun i =>
      ⟨L924.partner S i.val - n, by have := hSlt _ (hpart_spec i); omega⟩
    have hf_inj : Function.Injective f := by
      intro i j hij
      have hmemi := hpart_spec i
      have hmemj := hpart_spec j
      have hi2 := (hSlt _ hmemi).2.1
      have hj2 := (hSlt _ hmemj).2.1
      have hval : L924.partner S i.val = L924.partner S j.val := by
        have := congrArg Fin.val hij
        dsimp only [f] at this
        omega
      by_contra hne
      have hene : (i.val, L924.partner S i.val) ≠ (j.val, L924.partner S j.val) :=
        fun h => hne (Fin.ext (Prod.mk.inj h).1)
      exact Finset.disjoint_left.mp (hSm _ hmemi _ hmemj hene)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (by rw [hval]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
    have hσA : ∀ i : Fin n, A i (σ i) = true := by
      intro i
      obtain ⟨h1, h2, hAij⟩ := (hSlt _ (hpart_spec i)).2.2.2
      exact hAij
    refine ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσA⟩, ?_⟩
    ext ⟨a, b⟩
    simp only [Φ, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      rcases Prod.mk.inj hi with ⟨rfl, rfl⟩
      have hmem := hpart_spec i
      have hge := (hSlt _ hmem).2.1
      have hadd : n + (σ i).val = L924.partner S i.val := by
        show n + (L924.partner S i.val - n) = L924.partner S i.val
        omega
      rwa [hadd]
    · intro hab
      have h1 := (hSlt _ hab).1
      have hge := (hSlt _ hab).2.1
      refine ⟨⟨a, h1⟩, ?_⟩
      have hpf := L924.partner_fst hSm (fun g hg => by have := hSlt g hg; omega) hab
      have hadd : n + (σ ⟨a, h1⟩).val = b := by
        show n + (L924.partner S a - n) = b
        rw [hpf]; omega
      exact Prod.ext rfl hadd

theorem Z_mod_b_eq_permanent (n : ℕ) (hn : 0 < n) (A : Fin n → Fin n → Bool) :
    let v := 2 * n
    let L := 2 * (1 + v * ((v + 1).log2 + 1))
    let k := v * (L + 1)
    let b := Nat.fib (L + 2)
    let B : Matrix (Fin n) (Fin n) Nat := fun i j => (A i j).toNat
    let cells := (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))
    let base := (cells.filter (fun z => A z.1 z.2)).map (fun z =>
      (z.1.val * (L + 1), (n + z.2.val) * (L + 1)))
    let good := fun (x y : Nat) => (x, y) ∈ base ∨ (y = x + 1 ∧ x / (L + 1) = y / (L + 1))
    let ban := (List.range k).flatMap (fun x => ((List.range k).filter (fun y =>
      decide (x < y ∧ ¬ good x y))).map (fun y => (x, y)))
    let Fn := (Fin k → Bool) → (Fin k → Bool) → Bool
    let fits := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2 * k ∧
      PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
      ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
      ∀ e ∈ ban, f (fun i => decide (i.val = e.1 ∨ i.val = e.2)) (fun _ => false) = false
    Nat.card {f : Fn // fits f} % b = B.permanent := by
  intro v L k b B cells base good ban Fn fits
  rw [Z_eq_big_card n hn A]
  have hE := edgeSet_lt A
  have hfac : v.factorial < b := fact_lt_fib_L n
  have hb1 : 1 < b := lt_of_le_of_lt (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero v)) hfac
  have ha : Nat.fib (L + 1) ^ 2 % b = 1 := by
    have hkL : L = 2 * (1 + v * ((v + 1).log2 + 1)) := rfl
    have hbne : Nat.fib (2 * (1 + v * ((v + 1).log2 + 1)) + 2) ≠ 1 := Nat.ne_of_gt hb1
    show Nat.fib (L + 1) ^ 2 % Nat.fib (L + 2) = 1
    rw [hkL, L924.cassini_even (1 + v * ((v + 1).log2 + 1)), add_comm,
        Nat.add_mul_mod_self_right, Nat.one_mod_eq_one.mpr hbne]
  let old := (edgeSet A).powerset.filter L924.IsMatch
  let m : ℕ → ℕ := fun r => (old.filter (fun S => S.card = r)).card
  have hp2 := L924.part2 v L (edgeSet A) hE
  have hbe := L924.big_eq m (Nat.fib (L + 1)) b v
  have hv2 : v % 2 = 0 := by omega
  have hvd : v / 2 = n := by omega
  have hbig_eq_Q : (L924.bigF v L (edgeSet A)).card = L924.Q m (Nat.fib (L + 1)) b n := by
    rw [hp2, hbe, hv2, pow_zero, Nat.one_mul, hvd]
  have hmn_lt : m n < b :=
    lt_of_le_of_lt ((Finset.card_filter_le _ _).trans (L924.matchings_le_factorial v (edgeSet A) hE)) hfac
  rw [hbig_eq_Q, L924.Q_mod m ha hb1 n hmn_lt]
  exact m_n_eq_permanent n A

end PEqualNP.Outside.L_meta_32063.Bridge


namespace PEqualNP.Outside.L_meta_32063.Sim

open Turing

def Simulates {K : Type} [DecidableEq K] {σ : Type}
    (exec : σ × (K → List Bool) → σ × (K → List Bool))
    (cost : σ × (K → List Bool) → ℕ) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (entry : Λ)
    (body : ∀ (Λ' : Type), (Λ → Λ') → Λ' → Λ → TM2.Stmt (fun _ : K => Bool) Λ' σ),
    ∀ (Λ' : Type) (M : Λ' → TM2.Stmt (fun _ : K => Bool) Λ' σ)
      (inj : Λ → Λ') (cont : Λ'),
      (∀ a, M (inj a) = body Λ' inj cont a) →
      ∀ s : σ × (K → List Bool),
        (flip bind (TM2.step M))^[cost s]
          (some ⟨some (inj entry), s.1, s.2⟩) =
        some ⟨some cont, (exec s).1, (exec s).2⟩

def SimulatesBound {K : Type} [DecidableEq K] {σ : Type}
    (exec : σ × (K → List Bool) → σ × (K → List Bool))
    (B : σ × (K → List Bool) → ℕ) : Prop :=
  ∃ cost : σ × (K → List Bool) → ℕ, (∀ s, cost s ≤ B s) ∧ Simulates exec cost

theorem iter_add {α : Type} (f : α → Option α) (m n : ℕ) (a b : α) (c : Option α)
    (h1 : (flip bind f)^[n] (some a) = some b) (h2 : (flip bind f)^[m] (some b) = c) :
    (flip bind f)^[m + n] (some a) = c := by
  rw [Function.iterate_add_apply, h1, h2]

theorem one_step {K : Type} [DecidableEq K] {σ Λ : Type}
    (M : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) (l : Λ) (v : σ) (S : K → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (c : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (hq : M l = q) (hc : TM2.stepAux q v S = c) :
    (flip bind (TM2.step M))^[1] (some ⟨some l, v, S⟩) = some c := by
  subst hq hc; rfl

theorem sim_push {K : Type} [DecidableEq K] {σ : Type} (k : K) (f : σ → Bool) :
    Simulates (fun s => (s.1, Function.update s.2 k (f s.1 :: s.2 k))) (fun _ => 1) := by
  refine ⟨Unit, inferInstance, (), fun _ _ cont _ => .push k f (.goto fun _ => cont), ?_⟩
  intro Λ' M inj cont hM s
  exact one_step M _ _ _ _ _ (hM ()) rfl

theorem sim_pop {K : Type} [DecidableEq K] {σ : Type} (k : K) (f : σ → Option Bool → σ) :
    Simulates (fun s => (f s.1 (s.2 k).head?, Function.update s.2 k (s.2 k).tail)) (fun _ => 1) := by
  refine ⟨Unit, inferInstance, (), fun _ _ cont _ => .pop k f (.goto fun _ => cont), ?_⟩
  intro Λ' M inj cont hM s
  exact one_step M _ _ _ _ _ (hM ()) rfl

theorem sim_load {K : Type} [DecidableEq K] {σ : Type} (f : σ → σ) :
    Simulates (K := K) (fun s => (f s.1, s.2)) (fun _ => 1) := by
  refine ⟨Unit, inferInstance, (), fun _ _ cont _ => .load f (.goto fun _ => cont), ?_⟩
  intro Λ' M inj cont hM s
  exact one_step M _ _ _ _ _ (hM ()) rfl

theorem sim_seq {K : Type} [DecidableEq K] {σ : Type}
    {ep eq : σ × (K → List Bool) → σ × (K → List Bool)}
    {cp cq : σ × (K → List Bool) → ℕ}
    (hp : Simulates ep cp) (hq : Simulates eq cq) :
    Simulates (fun s => eq (ep s)) (fun s => cq (ep s) + cp s) := by
  rcases hp with ⟨Λp, hFp, ep0, bp, hbp⟩
  rcases hq with ⟨Λq, hFq, eq0, bq, hbq⟩
  refine ⟨Λp ⊕ Λq, @instFintypeSum _ _ hFp hFq, Sum.inl ep0,
    fun Λ' inj cont a => match a with
      | Sum.inl x => bp Λ' (fun u => inj (Sum.inl u)) (inj (Sum.inr eq0)) x
      | Sum.inr y => bq Λ' (fun u => inj (Sum.inr u)) cont y, ?_⟩
  intro Λ' M inj cont hM s
  have h1 := hbp Λ' M (fun u => inj (Sum.inl u)) (inj (Sum.inr eq0)) (fun x => hM (Sum.inl x)) s
  have h2 := hbq Λ' M (fun u => inj (Sum.inr u)) cont (fun y => hM (Sum.inr y)) (ep s)
  exact iter_add _ _ _ _ _ _ h1 h2

theorem sim_ite {K : Type} [DecidableEq K] {σ : Type}
    (c : σ → Bool)
    {ep eq : σ × (K → List Bool) → σ × (K → List Bool)}
    {cp cq : σ × (K → List Bool) → ℕ}
    (hp : Simulates ep cp) (hq : Simulates eq cq) :
    Simulates (fun s => if c s.1 then ep s else eq s)
      (fun s => (if c s.1 then cp s else cq s) + 1) := by
  rcases hp with ⟨Λp, hFp, ep0, bp, hbp⟩
  rcases hq with ⟨Λq, hFq, eq0, bq, hbq⟩
  refine ⟨Option (Λp ⊕ Λq), @instFintypeOption _ (@instFintypeSum _ _ hFp hFq), none,
    fun Λ' inj cont a => match a with
      | none => .branch c (.goto fun _ => inj (some (Sum.inl ep0)))
          (.goto fun _ => inj (some (Sum.inr eq0)))
      | some (Sum.inl x) => bp Λ' (fun u => inj (some (Sum.inl u))) cont x
      | some (Sum.inr y) => bq Λ' (fun u => inj (some (Sum.inr u))) cont y, ?_⟩
  intro Λ' M inj cont hM s
  have h0 := hM none
  cases hc : c s.1
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    have h2 := hbq Λ' M (fun u => inj (some (Sum.inr u))) cont (fun y => hM (some (Sum.inr y))) s
    refine iter_add _ _ 1 _ _ _ ?_ h2
    refine one_step M _ _ _ _ _ h0 ?_
    simp [TM2.stepAux, hc]
  · simp only [hc, ↓reduceIte]
    have h1 := hbp Λ' M (fun u => inj (some (Sum.inl u))) cont (fun x => hM (some (Sum.inl x))) s
    refine iter_add _ _ 1 _ _ _ ?_ h1
    refine one_step M _ _ _ _ _ h0 ?_
    simp [TM2.stepAux, hc]

def loopExec {K : Type} [DecidableEq K] {σ : Type}
    (k : K) (f : σ → Option Bool → σ) (c : σ → Bool)
    (eb : σ × (K → List Bool) → σ × (K → List Bool)) :
    List Bool → σ × (K → List Bool) → σ × (K → List Bool)
  | [], s => (f s.1 none, Function.update s.2 k [])
  | x :: l, s =>
    if c (f s.1 (some x)) then
      loopExec k f c eb l (eb (f s.1 (some x), Function.update s.2 k l))
    else
      (f s.1 (some x), Function.update s.2 k l)

def loopCost {K : Type} [DecidableEq K] {σ : Type}
    (k : K) (f : σ → Option Bool → σ) (c : σ → Bool)
    (eb : σ × (K → List Bool) → σ × (K → List Bool))
    (cb : σ × (K → List Bool) → ℕ) :
    List Bool → σ × (K → List Bool) → ℕ
  | [], _ => 1
  | x :: l, s =>
    if c (f s.1 (some x)) then
      loopCost k f c eb cb l (eb (f s.1 (some x), Function.update s.2 k l)) +
        (cb (f s.1 (some x), Function.update s.2 k l) + 1)
    else 1

theorem sim_loop {K : Type} [DecidableEq K] {σ : Type}
    (k : K) (f : σ → Option Bool → σ) (c : σ → Bool)
    {eb : σ × (K → List Bool) → σ × (K → List Bool)}
    {cb : σ × (K → List Bool) → ℕ}
    (hb : Simulates eb cb)
    (hnone : ∀ v, c (f v none) = false)
    (hnt : ∀ s, (eb s).2 k = s.2 k) :
    Simulates (fun s => loopExec k f c eb (s.2 k) s)
      (fun s => loopCost k f c eb cb (s.2 k) s) := by
  rcases hb with ⟨Λb, hFb, eb0, bb, hbb⟩
  refine ⟨Option Λb, @instFintypeOption _ hFb, none,
    fun Λ' inj cont a => match a with
      | none => .pop k f (.branch c (.goto fun _ => inj (some eb0)) (.goto fun _ => cont))
      | some x => bb Λ' (fun u => inj (some u)) (inj none) x, ?_⟩
  intro Λ' M inj cont hM s
  have h0 := hM none
  have key : ∀ (l : List Bool) (s : σ × (K → List Bool)), s.2 k = l →
      (flip bind (TM2.step M))^[loopCost k f c eb cb l s]
        (some ⟨some (inj none), s.1, s.2⟩) =
      some ⟨some cont, (loopExec k f c eb l s).1, (loopExec k f c eb l s).2⟩ := by
    intro l
    induction l with
    | nil =>
      intro s hl
      refine one_step M _ _ _ _ _ h0 ?_
      simp [TM2.stepAux, hl, hnone, loopExec]
    | cons x l ihl =>
      intro s hl
      cases hc : c (f s.1 (some x))
      · simp only [loopCost, loopExec, hc, Bool.false_eq_true, ↓reduceIte]
        refine one_step M _ _ _ _ _ h0 ?_
        simp [TM2.stepAux, hl, hc]
      · simp only [loopCost, loopExec, hc, ↓reduceIte]
        have hstep : (flip bind (TM2.step M))^[1] (some ⟨some (inj none), s.1, s.2⟩) =
            some ⟨some (inj (some eb0)), f s.1 (some x), Function.update s.2 k l⟩ := by
          refine one_step M _ _ _ _ _ h0 ?_
          simp [TM2.stepAux, hl, hc]
        have hbody := hbb Λ' M (fun u => inj (some u)) (inj none) (fun u => hM (some u))
          (f s.1 (some x), Function.update s.2 k l)
        have hk : (eb (f s.1 (some x), Function.update s.2 k l)).2 k = l := by
          rw [hnt]; simp
        have hrest := ihl (eb (f s.1 (some x), Function.update s.2 k l)) hk
        exact iter_add _ _ _ _ _ _ (iter_add _ _ 1 _ _ _ hstep hbody) hrest
  exact key (s.2 k) s rfl

def Indep {K : Type} [DecidableEq K] (k : K) (F : (K → List Bool) → (K → List Bool)) : Prop :=
  ∀ S l, F (Function.update S k l) = Function.update (F S) k l

theorem indep_self {K : Type} [DecidableEq K] {k : K} {F : (K → List Bool) → (K → List Bool)}
    (h : Indep k F) (S : K → List Bool) : F S k = S k := by
  have := h S (S k)
  rw [Function.update_eq_self] at this
  rw [this, Function.update_self]

theorem indep_id {K : Type} [DecidableEq K] (k : K) : Indep k (id : (K → List Bool) → _) :=
  fun _ _ => rfl

theorem indep_push {K : Type} [DecidableEq K] {k k' : K} (hne : k' ≠ k) (b : Bool) :
    Indep k (fun S : K → List Bool => Function.update S k' (b :: S k')) := by
  intro S l; funext j
  by_cases hj1 : j = k <;> by_cases hj2 : j = k' <;> simp_all

theorem indep_popDrop {K : Type} [DecidableEq K] {k k' : K} (hne : k' ≠ k) :
    Indep k (fun S : K → List Bool => Function.update S k' (S k').tail) := by
  intro S l; funext j
  by_cases hj1 : j = k <;> by_cases hj2 : j = k' <;> simp_all

theorem indep_seq {K : Type} [DecidableEq K] {k : K} {F1 F2 : (K → List Bool) → (K → List Bool)}
    (h1 : Indep k F1) (h2 : Indep k F2) : Indep k (fun S => F2 (F1 S)) := by
  intro S l; dsimp only; rw [h1 S l, h2 (F1 S) l]

def PureSB {K : Type} [DecidableEq K]
    (F : (K → List Bool) → (K → List Bool))
    (B : (K → List Bool) → ℕ) : Prop :=
  ∃ (g : (Bool × Bool) × (K → List Bool) → (Bool × Bool)),
    SimulatesBound (K := K) (σ := Bool × Bool) (fun s => (g s, F s.2)) (fun s => B s.2)

theorem psb_mono {K : Type} [DecidableEq K]
    {F : (K → List Bool) → (K → List Bool)}
    {B1 B2 : (K → List Bool) → ℕ}
    (h : PureSB F B1) (hle : ∀ S, B1 S ≤ B2 S) : PureSB F B2 := by
  rcases h with ⟨g, c, hc, hsim⟩
  exact ⟨g, c, fun s => (hc s).trans (hle s.2), hsim⟩

theorem psb_congr {K : Type} [DecidableEq K]
    {F1 F2 : (K → List Bool) → (K → List Bool)}
    {B : (K → List Bool) → ℕ}
    (h : PureSB F1 B) (heq : ∀ S, F1 S = F2 S) : PureSB F2 B := by
  have hfe : F1 = F2 := funext heq
  subst hfe; exact h

theorem psb_noop {K : Type} [DecidableEq K] :
    PureSB (K := K) id (fun _ => 1) :=
  ⟨fun s => s.1, fun _ => 1, fun _ => le_rfl, sim_load id⟩

theorem psb_push {K : Type} [DecidableEq K] (k : K) (b : Bool) :
    PureSB (fun S : K → List Bool => Function.update S k (b :: S k)) (fun _ => 1) :=
  ⟨fun s => s.1, fun _ => 1, fun _ => le_rfl, sim_push k (fun _ => b)⟩

theorem psb_popDrop {K : Type} [DecidableEq K] (k : K) :
    PureSB (fun S : K → List Bool => Function.update S k (S k).tail) (fun _ => 1) :=
  ⟨fun s => s.1, fun _ => 1, fun _ => le_rfl, sim_pop k (fun v _ => v)⟩

theorem psb_seq {K : Type} [DecidableEq K]
    {F1 F2 : (K → List Bool) → (K → List Bool)}
    {B1 B2 : (K → List Bool) → ℕ}
    (h1 : PureSB F1 B1) (h2 : PureSB F2 B2) :
    PureSB (fun S => F2 (F1 S)) (fun S => B2 (F1 S) + B1 S) := by
  rcases h1 with ⟨g1, c1, hc1, hs1⟩
  rcases h2 with ⟨g2, c2, hc2, hs2⟩
  refine ⟨fun s => g2 (g1 s, F1 s.2), fun s => c2 (g1 s, F1 s.2) + c1 s, ?_, sim_seq hs1 hs2⟩
  intro s
  exact Nat.add_le_add (hc2 (g1 s, F1 s.2)) (hc1 s)

theorem psb_branchPop {K : Type} [DecidableEq K] (k : K)
    {FN FF FT : (K → List Bool) → (K → List Bool)}
    {BN BF BT : (K → List Bool) → ℕ}
    (hN : PureSB FN BN) (hF : PureSB FF BF) (hT : PureSB FT BT) :
    PureSB
      (fun S => match S k with
        | [] => FN (Function.update S k [])
        | false :: l => FF (Function.update S k l)
        | true :: l => FT (Function.update S k l))
      (fun S => match S k with
        | [] => BN (Function.update S k []) + 2
        | false :: l => BF (Function.update S k l) + 3
        | true :: l => BT (Function.update S k l) + 3) := by
  rcases hN with ⟨gN, cN, hcN, hsN⟩
  rcases hF with ⟨gF, cF, hcF, hsF⟩
  rcases hT with ⟨gT, cT, hcT, hsT⟩
  let dec : (Bool × Bool) → Option Bool → (Bool × Bool) := fun _ o =>
    match o with | none => (false, false) | some b => (true, b)
  have hpop : Simulates (K := K) (σ := Bool × Bool)
      (fun s => (dec s.1 (s.2 k).head?, Function.update s.2 k (s.2 k).tail)) (fun _ => 1) :=
    sim_pop k dec
  have hinner := sim_ite (fun v : Bool × Bool => v.2) hsT hsF
  have houter := sim_ite (fun v : Bool × Bool => v.1) hinner hsN
  have hfull := sim_seq hpop houter
  refine ⟨fun s => match s.2 k with
      | [] => gN ((false, false), Function.update s.2 k [])
      | false :: l => gF ((true, false), Function.update s.2 k l)
      | true :: l => gT ((true, true), Function.update s.2 k l),
    fun s => match s.2 k with
      | [] => cN ((false, false), Function.update s.2 k []) + 2
      | false :: l => cF ((true, false), Function.update s.2 k l) + 3
      | true :: l => cT ((true, true), Function.update s.2 k l) + 3,
    ?_, ?_⟩
  · intro s
    cases hk : s.2 k with
    | nil =>
      have h := hcN ((false, false), Function.update s.2 k []); dsimp only at h ⊢; simp only [hk]; omega
    | cons b l =>
      cases b
      · have h := hcF ((true, false), Function.update s.2 k l); dsimp only at h ⊢; simp only [hk]; omega
      · have h := hcT ((true, true), Function.update s.2 k l); dsimp only at h ⊢; simp only [hk]; omega
  · have he1 : (fun s : (Bool × Bool) × (K → List Bool) =>
        if (dec s.1 (s.2 k).head?).1 then
          if (dec s.1 (s.2 k).head?).2 then
            (gT (dec s.1 (s.2 k).head?, Function.update s.2 k (s.2 k).tail),
             FT (Function.update s.2 k (s.2 k).tail))
          else
            (gF (dec s.1 (s.2 k).head?, Function.update s.2 k (s.2 k).tail),
             FF (Function.update s.2 k (s.2 k).tail))
        else
          (gN (dec s.1 (s.2 k).head?, Function.update s.2 k (s.2 k).tail),
           FN (Function.update s.2 k (s.2 k).tail))) =
        (fun s => (match s.2 k with
          | [] => gN ((false, false), Function.update s.2 k [])
          | false :: l => gF ((true, false), Function.update s.2 k l)
          | true :: l => gT ((true, true), Function.update s.2 k l),
          match s.2 k with
          | [] => FN (Function.update s.2 k [])
          | false :: l => FF (Function.update s.2 k l)
          | true :: l => FT (Function.update s.2 k l))) := by
      funext s; cases hk : s.2 k with
      | nil => simp [dec]
      | cons b l => cases b <;> simp [dec]
    have he2 : (fun s : (Bool × Bool) × (K → List Bool) =>
        (if (dec s.1 (s.2 k).head?).1 then
          (if (dec s.1 (s.2 k).head?).2 then
            cT (dec s.1 (s.2 k).head?, Function.update s.2 k (s.2 k).tail)
          else
            cF (dec s.1 (s.2 k).head?, Function.update s.2 k (s.2 k).tail)) + 1
        else
          cN (dec s.1 (s.2 k).head?, Function.update s.2 k (s.2 k).tail)) + 1 + 1) =
        (fun s => match s.2 k with
          | [] => cN ((false, false), Function.update s.2 k []) + 2
          | false :: l => cF ((true, false), Function.update s.2 k l) + 3
          | true :: l => cT ((true, true), Function.update s.2 k l) + 3) := by
      funext s; cases hk : s.2 k with
      | nil => simp [dec]
      | cons b l => cases b <;> simp [dec]
    rw [← he1, ← he2]
    exact hfull

def forEachCost {K : Type} [DecidableEq K] (k : K)
    (step : Bool → (K → List Bool) → (K → List Bool))
    (B : Bool → (K → List Bool) → ℕ) :
    List Bool → (K → List Bool) → ℕ
  | [], _ => 1
  | b :: l, S =>
    forEachCost k step B l (step b (Function.update S k l)) +
      (B b (Function.update S k l) + 2)

theorem psb_forEach {K : Type} [DecidableEq K] (k : K)
    {step : Bool → (K → List Bool) → (K → List Bool)}
    {B : Bool → (K → List Bool) → ℕ}
    (hF : PureSB (step false) (B false))
    (hT : PureSB (step true) (B true))
    (hind : ∀ b, Indep k (step b)) :
    PureSB
      (fun S => (S k).foldl (fun S' b => step b S') (Function.update S k []))
      (fun S => forEachCost k step B (S k) S) := by
  rcases hF with ⟨gF, cF, hcF, hsF⟩
  rcases hT with ⟨gT, cT, hcT, hsT⟩
  let dec : (Bool × Bool) → Option Bool → (Bool × Bool) := fun _ o =>
    match o with | none => (false, false) | some b => (true, b)
  let eb : (Bool × Bool) × (K → List Bool) → (Bool × Bool) × (K → List Bool) :=
    fun s => if s.1.2 then (gT s, step true s.2) else (gF s, step false s.2)
  let cb : (Bool × Bool) × (K → List Bool) → ℕ :=
    fun s => (if s.1.2 then cT s else cF s) + 1
  have hbody : Simulates eb cb := sim_ite (fun v => v.2) hsT hsF
  have hnt : ∀ s, (eb s).2 k = s.2 k := by
    intro s; simp only [eb]; split <;> exact indep_self (hind _) _
  have hloop := sim_loop k dec (fun v => v.1) hbody (fun _ => rfl) hnt
  have hexec : ∀ (l : List Bool) (s : (Bool × Bool) × (K → List Bool)),
      (loopExec k dec (fun v => v.1) eb l s).2 =
        l.foldl (fun S' b => step b S') (Function.update s.2 k []) := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons b l ihl =>
      intro s
      have hc : (dec s.1 (some b)).1 = true := rfl
      simp only [loopExec, hc, ↓reduceIte, List.foldl_cons]
      rw [ihl]
      have hst : (eb (dec s.1 (some b), Function.update s.2 k l)).2 =
          step b (Function.update s.2 k l) := by
        cases b <;> rfl
      rw [hst, hind b, Function.update_idem, hind b]
  have hcost : ∀ (l : List Bool) (s : (Bool × Bool) × (K → List Bool)),
      loopCost k dec (fun v => v.1) eb cb l s ≤ forEachCost k step B l s.2 := by
    intro l
    induction l with
    | nil => intro _; exact le_rfl
    | cons b l ihl =>
      intro s
      have hc : (dec s.1 (some b)).1 = true := rfl
      simp only [loopCost, hc, ↓reduceIte, forEachCost]
      have hst : (eb (dec s.1 (some b), Function.update s.2 k l)).2 =
          step b (Function.update s.2 k l) := by
        cases b <;> rfl
      have h1 := ihl (eb (dec s.1 (some b), Function.update s.2 k l))
      rw [hst] at h1
      have h2 : cb (dec s.1 (some b), Function.update s.2 k l) ≤ B b (Function.update s.2 k l) + 1 := by
        cases b
        · exact Nat.add_le_add_right (hcF _) 1
        · exact Nat.add_le_add_right (hcT _) 1
      omega
  refine ⟨fun s => (loopExec k dec (fun v => v.1) eb (s.2 k) s).1,
    fun s => loopCost k dec (fun v => v.1) eb cb (s.2 k) s,
    fun s => hcost (s.2 k) s, ?_⟩
  have hfun : (fun s : (Bool × Bool) × (K → List Bool) => loopExec k dec (fun v => v.1) eb (s.2 k) s) =
      (fun s => ((loopExec k dec (fun v => v.1) eb (s.2 k) s).1,
        (s.2 k).foldl (fun S' b => step b S') (Function.update s.2 k []))) := by
    funext s
    exact Prod.ext rfl (hexec (s.2 k) s)
  rw [← hfun]
  exact hloop

theorem psb_forEachIgn {K : Type} [DecidableEq K] (k : K)
    {step : (K → List Bool) → (K → List Bool)}
    {B : (K → List Bool) → ℕ}
    (h : PureSB step B) (hind : Indep k step) :
    PureSB
      (fun S => (S k).foldl (fun S' _ => step S') (Function.update S k []))
      (fun S => forEachCost k (fun _ => step) (fun _ => B) (S k) S) :=
  psb_forEach k (step := fun _ => step) (B := fun _ => B) h h (fun _ => hind)

theorem forEachCost_le {K : Type} [DecidableEq K] (k : K)
    (step : Bool → (K → List Bool) → (K → List Bool))
    (B : Bool → (K → List Bool) → ℕ)
    (Inv : (K → List Bool) → Prop) (M : ℕ)
    (hinv : ∀ b S, Inv S → Inv (step b S))
    (hB : ∀ b S, Inv S → B b S ≤ M)
    (hupd : ∀ S l, Inv S → Inv (Function.update S k l)) :
    ∀ (l : List Bool) (S : K → List Bool), Inv S →
      forEachCost k step B l S ≤ l.length * (M + 2) + 1 := by
  intro l
  induction l with
  | nil => intro _ _; simp [forEachCost]
  | cons b l ihl =>
    intro S hS
    simp only [forEachCost, List.length_cons]
    have hS' : Inv (Function.update S k l) := hupd S l hS
    have h1 := ihl (step b (Function.update S k l)) (hinv b _ hS')
    have h2 := hB b _ hS'
    have hmul : (l.length + 1) * (M + 2) = l.length * (M + 2) + 1 * (M + 2) := Nat.add_mul _ _ _
    omega

def whilePop3Exec {K : Type} [DecidableEq K] (k : K) (pred : Bool → Bool)
    (step onStopFalse onStopNil : (K → List Bool) → (K → List Bool)) :
    List Bool → (K → List Bool) → (K → List Bool)
  | [], S => onStopNil (Function.update S k [])
  | b :: l, S =>
    if pred b then
      whilePop3Exec k pred step onStopFalse onStopNil l (step (Function.update S k l))
    else
      onStopFalse (Function.update S k l)

def whilePop3Cost {K : Type} [DecidableEq K] (k : K) (pred : Bool → Bool)
    (step : (K → List Bool) → (K → List Bool))
    (Bs BF BN : (K → List Bool) → ℕ) :
    List Bool → (K → List Bool) → ℕ
  | [], S => BN (Function.update S k []) + 2
  | b :: l, S =>
    if pred b then
      whilePop3Cost k pred step Bs BF BN l (step (Function.update S k l)) +
        (Bs (Function.update S k l) + 1)
    else
      BF (Function.update S k l) + 2

theorem psb_whilePop3 {K : Type} [DecidableEq K] (k : K) (pred : Bool → Bool)
    {step onStopFalse onStopNil : (K → List Bool) → (K → List Bool)}
    {Bs BF BN : (K → List Bool) → ℕ}
    (hs : PureSB step Bs)
    (hF : PureSB onStopFalse BF)
    (hN : PureSB onStopNil BN)
    (hind : Indep k step) :
    PureSB
      (fun S => whilePop3Exec k pred step onStopFalse onStopNil (S k) S)
      (fun S => whilePop3Cost k pred step Bs BF BN (S k) S) := by
  rcases hs with ⟨gs, cs, hcs, hss⟩
  rcases hF with ⟨gF, cF, hcF, hsF⟩
  rcases hN with ⟨gN, cN, hcN, hsN⟩
  let dec : (Bool × Bool) → Option Bool → (Bool × Bool) := fun _ o =>
    match o with
    | none => (false, false)
    | some b => if pred b then (true, true) else (false, true)
  have hnt : ∀ s : (Bool × Bool) × (K → List Bool), step s.2 k = s.2 k :=
    fun s => indep_self hind s.2
  have hloop := sim_loop k dec (fun v => v.1) hss (fun _ => rfl) hnt
  have hfin := sim_ite (fun v : Bool × Bool => v.2) hsF hsN
  have hfull := sim_seq hloop hfin
  have hres : ∀ (l : List Bool) (s : (Bool × Bool) × (K → List Bool)),
      (let t := loopExec k dec (fun v => v.1) (fun u => (gs u, step u.2)) l s
       (if t.1.2 then (gF t, onStopFalse t.2) else (gN t, onStopNil t.2)).2 =
         whilePop3Exec k pred step onStopFalse onStopNil l s.2 ∧
       (if t.1.2 then cF t else cN t) + 1 +
         loopCost k dec (fun v => v.1) (fun u => (gs u, step u.2)) cs l s ≤
         whilePop3Cost k pred step Bs BF BN l s.2) := by
    intro l
    induction l with
    | nil =>
      intro s
      dsimp only
      simp only [loopExec, loopCost, dec, Bool.false_eq_true, ↓reduceIte, whilePop3Exec, whilePop3Cost]
      have h := hcN ((false, false), Function.update s.2 k [])
      dsimp only at h
      exact ⟨trivial, by omega⟩
    | cons b l ihl =>
      intro s
      dsimp only
      cases hp : pred b
      · simp only [loopExec, loopCost, dec, hp, Bool.false_eq_true, ↓reduceIte, whilePop3Exec, whilePop3Cost]
        have h := hcF ((false, true), Function.update s.2 k l)
        dsimp only at h
        exact ⟨trivial, by omega⟩
      · simp only [loopExec, loopCost, dec, hp, ↓reduceIte, whilePop3Exec, whilePop3Cost]
        have h1 := ihl (gs ((true, true), Function.update s.2 k l), step (Function.update s.2 k l))
        have h2 := hcs ((true, true), Function.update s.2 k l)
        dsimp only [dec] at h1 h2 ⊢
        exact ⟨h1.1, by have h12 := h1.2; omega⟩
  refine ⟨fun s =>
      let t := loopExec k dec (fun v => v.1) (fun u => (gs u, step u.2)) (s.2 k) s
      if t.1.2 then gF t else gN t,
    fun s =>
      let t := loopExec k dec (fun v => v.1) (fun u => (gs u, step u.2)) (s.2 k) s
      (if t.1.2 then cF t else cN t) + 1 +
        loopCost k dec (fun v => v.1) (fun u => (gs u, step u.2)) cs (s.2 k) s,
    fun s => (hres (s.2 k) s).2, ?_⟩
  have hfun : (fun s : (Bool × Bool) × (K → List Bool) =>
      let t := loopExec k dec (fun v => v.1) (fun u => (gs u, step u.2)) (s.2 k) s
      if t.1.2 then (gF t, onStopFalse t.2) else (gN t, onStopNil t.2)) =
      (fun s =>
        (let t := loopExec k dec (fun v => v.1) (fun u => (gs u, step u.2)) (s.2 k) s
         if t.1.2 then gF t else gN t,
         whilePop3Exec k pred step onStopFalse onStopNil (s.2 k) s.2)) := by
    funext s
    refine Prod.ext ?_ (hres (s.2 k) s).1
    dsimp only
    split <;> rfl
  rw [← hfun]
  exact hfull

theorem psb_to_polyTime {K : Type} [DecidableEq K] [Fintype K] (kIn kOut : K)
    {F : (K → List Bool) → (K → List Bool)}
    {B : (K → List Bool) → ℕ}
    (h : PureSB F B)
    (f : List Bool → List Bool)
    (P : Polynomial ℕ)
    (hout : ∀ x : List Bool,
      F (Function.update (fun _ : K => ([] : List Bool)) kIn x) =
        Function.update (fun _ : K => ([] : List Bool)) kOut (f x))
    (htime : ∀ x : List Bool,
      1 + B (Function.update (fun _ : K => ([] : List Bool)) kIn x) ≤ P.eval x.length) :
    ∃ M : TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
      ∀ i, Finite (M.tm.Γ i) := by
  rcases h with ⟨g, c, hc, Λ, hFΛ, entry, body, hsim⟩
  let tm : FinTM2 :=
    { K := K
      k₀ := kIn
      k₁ := kOut
      Γ := fun _ => Bool
      Λ := Option Λ
      main := some entry
      σ := Bool × Bool
      initialState := (false, false)
      Γk₀Fin := inferInstanceAs (Fintype Bool)
      m := fun l => match l with
        | some a => body (Option Λ) some none a
        | none => .load (fun _ => (false, false)) .halt }
  have hinit : ∀ x : List Bool, initList tm x =
      ⟨some (some entry), (false, false), Function.update (fun _ : K => []) kIn x⟩ := by
    intro x
    unfold initList
    congr 1
    funext k
    by_cases hk : k = kIn <;> simp [tm, hk]
  have hhalt : ∀ y : List Bool, haltList tm y =
      ⟨none, (false, false), Function.update (fun _ : K => []) kOut y⟩ := by
    intro y
    unfold haltList
    congr 1
    funext k
    by_cases hk : k = kOut <;> simp [tm, hk]
  have hrun : ∀ x : List Bool,
      (flip bind (TM2.step tm.m))^[1 + c ((false, false), Function.update (fun _ : K => []) kIn x)]
        (some (initList tm x)) = some (haltList tm (f x)) := by
    intro x
    rw [hinit, hhalt]
    have h1 := hsim (Option Λ) tm.m some none (fun _ => rfl)
      ((false, false), Function.update (fun _ : K => []) kIn x)
    have h2 : (flip bind (TM2.step tm.m))^[1]
        (some ⟨some none, g ((false, false), Function.update (fun _ : K => []) kIn x),
          F (Function.update (fun _ : K => []) kIn x)⟩) =
        some ⟨none, (false, false), Function.update (fun _ : K => []) kOut (f x)⟩ := by
      rw [hout x]
      exact one_step tm.m none _ _ (.load (fun _ => (false, false)) .halt) _ rfl rfl
    exact iter_add _ _ _ _ _ _ h1 h2
  refine ⟨{
    tm := tm
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    time := P
    outputsFun := fun x =>
      { steps := 1 + c ((false, false), Function.update (fun _ : K => []) kIn x)
        evals_in_steps := by
          have hm1 : List.map (Equiv.refl Bool).invFun x = x := List.map_id x
          have hm2 : List.map (Equiv.refl Bool).invFun (f x) = f x := List.map_id (f x)
          rw [hm1, hm2]
          exact hrun x
        steps_le_m := by
          have h1 := hc ((false, false), Function.update (fun _ : K => []) kIn x)
          dsimp only at h1
          have h2 := htime x
          omega } }, fun _ => (inferInstance : Finite Bool)⟩

def clearExec {K : Type} [DecidableEq K] (a : K) (S : K → List Bool) : K → List Bool :=
  Function.update S a []

theorem psb_clear {K : Type} [DecidableEq K] (a : K) :
    PureSB (clearExec a) (fun S => 3 * (S a).length + 1) := by
  have h := psb_forEach a (step := fun _ S => S) (B := fun _ _ => 1)
    psb_noop psb_noop (fun _ => indep_id a)
  refine psb_mono (psb_congr h ?_) ?_
  · intro S
    have hf : ∀ (l : List Bool) (T : K → List Bool), l.foldl (fun S' _ => S') T = T := by
      intro l; induction l with | nil => intro _; rfl | cons _ l ih => intro T; exact ih T
    exact hf (S a) _
  · intro S
    have hc := forEachCost_le a (fun _ S => S) (fun _ _ => 1) (fun _ => True) 1
      (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial) (S a) S trivial
    omega

theorem indep_clear {K : Type} [DecidableEq K] {k a : K} (hne : a ≠ k) :
    Indep k (clearExec a) := by
  intro S l; funext j; simp only [clearExec]
  by_cases h1 : j = k <;> by_cases h2 : j = a <;> simp_all

def revMoveExec {K : Type} [DecidableEq K] (a b : K) (S : K → List Bool) : K → List Bool :=
  Function.update (Function.update S a []) b ((S a).reverse ++ S b)

theorem psb_revMove {K : Type} [DecidableEq K] {a b : K} (hab : a ≠ b) :
    PureSB (revMoveExec a b) (fun S => 3 * (S a).length + 1) := by
  have h := psb_forEach a
    (step := fun x S => Function.update S b (x :: S b))
    (B := fun _ _ => 1)
    (psb_push b false) (psb_push b true)
    (fun x => indep_push hab.symm x)
  refine psb_mono (psb_congr h ?_) ?_
  · intro S
    have hf : ∀ (l : List Bool) (T : K → List Bool),
        l.foldl (fun S' x => Function.update S' b (x :: S' b)) T =
          Function.update T b (l.reverse ++ T b) := by
      intro l
      induction l with
      | nil => intro T; simp [Function.update_eq_self]
      | cons x l ih =>
        intro T
        simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        rw [ih, Function.update_self, Function.update_idem]
    rw [hf, Function.update_of_ne hab.symm]; rfl
  · intro S
    have hc := forEachCost_le a (fun x S => Function.update S b (x :: S b)) (fun _ _ => 1)
      (fun _ => True) 1 (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial) (S a) S trivial
    omega

theorem indep_revMove {K : Type} [DecidableEq K] {k a b : K} (ha : a ≠ k) (hb : b ≠ k) :
    Indep k (revMoveExec a b) := by
  intro S l; funext j; simp only [revMoveExec]
  by_cases h1 : j = k <;> by_cases h2 : j = b <;> by_cases h3 : j = a <;> simp_all

def revCopy2Exec {K : Type} [DecidableEq K] (a b c : K) (S : K → List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update S a []) b ((S a).reverse ++ S b))
    c ((S a).reverse ++ S c)

theorem psb_revCopy2 {K : Type} [DecidableEq K] {a b c : K}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    PureSB (revCopy2Exec a b c) (fun S => 4 * (S a).length + 1) := by
  let st : Bool → (K → List Bool) → (K → List Bool) :=
    fun x S => Function.update (Function.update S b (x :: S b)) c (x :: S c)
  have hst : ∀ x : Bool, PureSB (st x) (fun _ => 2) := fun x => by
    have h1 := psb_seq (psb_push b x) (psb_push c x)
    refine psb_congr h1 ?_
    intro S; simp only [st, Function.update_of_ne hbc.symm]
  have hind : ∀ x : Bool, Indep a (st x) := fun x => by
    intro S l; funext j; simp only [st]
    by_cases h1 : j = a <;> by_cases h2 : j = c <;> by_cases h3 : j = b <;> simp_all
  have h := psb_forEach a (step := st) (B := fun _ _ => 2) (hst false) (hst true) hind
  refine psb_mono (psb_congr h ?_) ?_
  · intro S
    have hf : ∀ (l : List Bool) (T : K → List Bool),
        l.foldl (fun S' x => st x S') T =
          Function.update (Function.update T b (l.reverse ++ T b)) c (l.reverse ++ T c) := by
      intro l
      induction l with
      | nil => intro T; simp [Function.update_eq_self]
      | cons x l ih =>
        intro T
        simp only [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        rw [ih]
        funext j; simp only [st]
        by_cases h1 : j = c <;> by_cases h2 : j = b <;> simp_all
    rw [hf, Function.update_of_ne hab.symm, Function.update_of_ne hac.symm]; rfl
  · intro S
    have hc := forEachCost_le a st (fun _ _ => 2) (fun _ => True) 2
      (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial) (S a) S trivial
    omega

theorem indep_revCopy2 {K : Type} [DecidableEq K] {k a b c : K}
    (ha : a ≠ k) (hb : b ≠ k) (hc : c ≠ k) :
    Indep k (revCopy2Exec a b c) := by
  intro S l; funext j; simp only [revCopy2Exec]
  by_cases h1 : j = k <;> by_cases h2 : j = c <;> by_cases h3 : j = b <;> by_cases h4 : j = a <;> simp_all

def copyExec {K : Type} [DecidableEq K] (a b tmp : K) (S : K → List Bool) : K → List Bool :=
  revCopy2Exec tmp a b (revMoveExec a tmp S)

theorem copyExec_of_empty {K : Type} [DecidableEq K] {a b tmp : K}
    (hab : a ≠ b) (hat : a ≠ tmp) (hbt : b ≠ tmp) (S : K → List Bool) (ht : S tmp = []) :
    copyExec a b tmp S = Function.update S b (S a ++ S b) := by
  funext j
  simp only [copyExec, revCopy2Exec, revMoveExec]
  by_cases h1 : j = b <;> by_cases h2 : j = a <;> by_cases h3 : j = tmp <;> simp_all

theorem psb_copy {K : Type} [DecidableEq K] {a b tmp : K}
    (hab : a ≠ b) (hat : a ≠ tmp) (hbt : b ≠ tmp) :
    PureSB (copyExec a b tmp) (fun S => 7 * (S a).length + 4 * (S tmp).length + 2) := by
  have h := psb_seq (psb_revMove hat) (psb_revCopy2 hat.symm hbt.symm hab)
  refine psb_mono h ?_
  intro S
  simp only [revMoveExec, Function.update_self, List.length_append, List.length_reverse]
  omega

theorem indep_copy {K : Type} [DecidableEq K] {k a b tmp : K}
    (ha : a ≠ k) (hb : b ≠ k) (ht : tmp ≠ k) :
    Indep k (copyExec a b tmp) := by
  intro S l; simp only [copyExec]; rw [indep_revMove ha ht, indep_revCopy2 ht ha hb]

def revCopyExec {K : Type} [DecidableEq K] (a b tmp : K) (S : K → List Bool) : K → List Bool :=
  revMoveExec tmp a (revCopy2Exec a b tmp S)

theorem revCopyExec_of_empty {K : Type} [DecidableEq K] {a b tmp : K}
    (hab : a ≠ b) (hat : a ≠ tmp) (hbt : b ≠ tmp) (S : K → List Bool) (ht : S tmp = []) :
    revCopyExec a b tmp S = Function.update S b ((S a).reverse ++ S b) := by
  funext j
  simp only [revCopyExec, revMoveExec, revCopy2Exec]
  by_cases h1 : j = a <;> by_cases h2 : j = tmp <;> by_cases h3 : j = b <;> simp_all

theorem psb_revCopy {K : Type} [DecidableEq K] {a b tmp : K}
    (hab : a ≠ b) (hat : a ≠ tmp) (hbt : b ≠ tmp) :
    PureSB (revCopyExec a b tmp) (fun S => 7 * (S a).length + 3 * (S tmp).length + 2) := by
  have h := psb_seq (psb_revCopy2 hab hat hbt) (psb_revMove hat.symm)
  refine psb_mono h ?_
  intro S
  simp only [revCopy2Exec, Function.update_self, List.length_append, List.length_reverse]
  omega

theorem indep_revCopy {K : Type} [DecidableEq K] {k a b tmp : K}
    (ha : a ≠ k) (hb : b ≠ k) (ht : tmp ≠ k) :
    Indep k (revCopyExec a b tmp) := by
  intro S l; simp only [revCopyExec]; rw [indep_revCopy2 ha hb ht, indep_revMove ht ha]

def incBits : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incBits l

def incFixedBits : List Bool → List Bool
  | [] => []
  | false :: l => true :: l
  | true :: l => false :: incFixedBits l

theorem replicate_append_cons {α : Type} (a : α) (pref : List α) :
    ∀ n : ℕ, List.replicate n a ++ a :: pref = a :: (List.replicate n a ++ pref)
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, replicate_append_cons a pref n]

def incBinExec {K : Type} [DecidableEq K] (x tmp : K) (S : K → List Bool) : K → List Bool :=
  revMoveExec tmp x (whilePop3Exec x id
    (fun T => Function.update T tmp (false :: T tmp))
    (fun T => Function.update T tmp (true :: T tmp))
    (fun T => Function.update T tmp (true :: T tmp))
    (S x) S)

theorem incBinExec_of_empty {K : Type} [DecidableEq K] {x tmp : K} (hxt : x ≠ tmp)
    (S : K → List Bool) (ht : S tmp = []) :
    incBinExec x tmp S = Function.update S x (incBits (S x)) := by
  have key : ∀ (l pref : List Bool) (T : K → List Bool), T x = l → T tmp = pref →
      whilePop3Exec x id
        (fun U => Function.update U tmp (false :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp)) l T =
      Function.update (Function.update T x (l.dropWhile id).tail) tmp
        (true :: List.replicate (l.takeWhile id).length false ++ pref) := by
    intro l
    induction l with
    | nil =>
      intro pref T _ htp
      funext j; simp only [whilePop3Exec, List.dropWhile_nil, List.tail_nil, List.takeWhile_nil,
        List.length_nil, List.replicate_zero, List.cons_append, List.nil_append]
      by_cases h1 : j = tmp <;> by_cases h2 : j = x <;> simp_all
    | cons b l ih =>
      intro pref T _ htp
      cases b
      · funext j; simp only [whilePop3Exec, id_eq, Bool.false_eq_true, ↓reduceIte,
          List.dropWhile_cons, List.tail_cons, List.takeWhile_cons, List.length_nil,
          List.replicate_zero, List.cons_append, List.nil_append]
        by_cases h1 : j = tmp <;> by_cases h2 : j = x <;> simp_all
      · simp only [whilePop3Exec, id_eq, ↓reduceIte, List.dropWhile_cons, List.takeWhile_cons,
          List.length_cons, List.replicate_succ]
        rw [ih (false :: pref) _ (by simp [hxt]) (by simp [hxt.symm, htp])]
        funext j
        by_cases h1 : j = tmp <;> by_cases h2 : j = x <;>
          simp_all [List.cons_append, List.append_assoc, replicate_append_cons]
  have hinc : ∀ l : List Bool,
      (true :: List.replicate (l.takeWhile id).length false).reverse ++ (l.dropWhile id).tail =
        incBits l := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih =>
      cases b
      · simp [incBits]
      · simp only [incBits, List.takeWhile_cons, id_eq, ↓reduceIte, List.length_cons,
          List.replicate_succ, List.dropWhile_cons]
        rw [← ih]
        simp only [List.reverse_cons, List.reverse_replicate, List.append_assoc, List.singleton_append,
          List.cons_append]
        exact replicate_append_cons _ _ _
  simp only [incBinExec]
  rw [key (S x) [] S rfl ht]
  funext j
  simp only [revMoveExec, List.append_nil]
  by_cases h1 : j = x <;> by_cases h2 : j = tmp <;> simp_all

theorem psb_incBin {K : Type} [DecidableEq K] {x tmp : K} (hxt : x ≠ tmp) :
    PureSB (incBinExec x tmp) (fun S => 5 * (S x).length + 3 * (S tmp).length + 7) := by
  have hw := psb_whilePop3 x id (psb_push tmp false) (psb_push tmp true) (psb_push tmp true)
    (indep_push hxt.symm false)
  have hfull := psb_seq hw (psb_revMove hxt.symm)
  refine psb_mono hfull ?_
  intro S
  have h1 : ∀ (l : List Bool) (T : K → List Bool),
      whilePop3Cost x id (fun U => Function.update U tmp (false :: U tmp))
        (fun _ => 1) (fun _ => 1) (fun _ => 1) l T ≤ 2 * l.length + 3 ∧
      ((whilePop3Exec x id (fun U => Function.update U tmp (false :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp)) l T) tmp).length ≤ l.length + (T tmp).length + 1 := by
    intro l
    induction l with
    | nil =>
      intro T
      simp only [whilePop3Cost, whilePop3Exec, Function.update_self, Function.update_of_ne hxt.symm,
        List.length_cons, List.length_nil]
      exact ⟨by omega, by omega⟩
    | cons b l ih =>
      intro T
      cases b
      · simp only [whilePop3Cost, whilePop3Exec, id_eq, Bool.false_eq_true, ↓reduceIte,
          Function.update_self, Function.update_of_ne hxt.symm, List.length_cons]
        exact ⟨by omega, by omega⟩
      · simp only [whilePop3Cost, whilePop3Exec, id_eq, ↓reduceIte, List.length_cons,
          Function.update_of_ne hxt.symm]
        have hih := ih (Function.update (Function.update T x l) tmp (false :: T tmp))
        simp only [Function.update_self, List.length_cons] at hih
        exact ⟨by have := hih.1; omega, by have := hih.2; omega⟩
  have := h1 (S x) S
  omega

theorem indep_incBin {K : Type} [DecidableEq K] {k x tmp : K} (hx : x ≠ k) (ht : tmp ≠ k) :
    Indep k (incBinExec x tmp) := by
  intro S l
  simp only [incBinExec]
  have key : ∀ (m : List Bool) (T : K → List Bool),
      whilePop3Exec x id (fun U => Function.update U tmp (false :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp)) m (Function.update T k l) =
      Function.update (whilePop3Exec x id (fun U => Function.update U tmp (false :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp)) m T) k l := by
    intro m
    induction m with
    | nil =>
      intro T; funext j; simp only [whilePop3Exec]
      by_cases h1 : j = k <;> by_cases h2 : j = tmp <;> by_cases h3 : j = x <;> simp_all
    | cons b m ih =>
      intro T; cases b
      · funext j; simp only [whilePop3Exec, id_eq, Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : j = k <;> by_cases h2 : j = tmp <;> by_cases h3 : j = x <;> simp_all
      · simp only [whilePop3Exec, id_eq, ↓reduceIte]
        have hstep : Function.update (Function.update (Function.update T k l) x m) tmp
            (false :: Function.update (Function.update T k l) x m tmp) =
            Function.update (Function.update (Function.update T x m) tmp
              (false :: Function.update T x m tmp)) k l := by
          funext j; by_cases h1 : j = k <;> by_cases h2 : j = tmp <;> by_cases h3 : j = x <;> simp_all
        rw [hstep, ih]
  rw [Function.update_of_ne hx, key (S x) S, indep_revMove ht hx]

def incFixedExec {K : Type} [DecidableEq K] (x tmp : K) (S : K → List Bool) : K → List Bool :=
  revMoveExec tmp x (whilePop3Exec x id
    (fun T => Function.update T tmp (false :: T tmp))
    (fun T => Function.update T tmp (true :: T tmp))
    id (S x) S)

theorem incFixedExec_of_empty {K : Type} [DecidableEq K] {x tmp : K} (hxt : x ≠ tmp)
    (S : K → List Bool) (ht : S tmp = []) :
    incFixedExec x tmp S = Function.update S x (incFixedBits (S x)) := by
  have key : ∀ (l pref : List Bool) (T : K → List Bool), T x = l → T tmp = pref →
      whilePop3Exec x id
        (fun U => Function.update U tmp (false :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp))
        id l T =
      if l.dropWhile id = [] then
        Function.update (Function.update T x []) tmp (List.replicate l.length false ++ pref)
      else
        Function.update (Function.update T x (l.dropWhile id).tail) tmp
          (true :: List.replicate (l.takeWhile id).length false ++ pref) := by
    intro l
    induction l with
    | nil =>
      intro pref T _ htp
      funext j; simp only [whilePop3Exec, id_eq, List.dropWhile_nil, ↓reduceIte, List.length_nil,
        List.replicate_zero, List.nil_append]
      by_cases h1 : j = tmp <;> by_cases h2 : j = x <;> simp_all
    | cons b l ih =>
      intro pref T _ htp
      cases b
      · funext j; simp only [whilePop3Exec, id_eq, Bool.false_eq_true, ↓reduceIte,
          List.dropWhile_cons, List.cons_ne_nil, List.tail_cons, List.takeWhile_cons,
          List.length_nil, List.replicate_zero, List.cons_append, List.nil_append]
        by_cases h1 : j = tmp <;> by_cases h2 : j = x <;> simp_all
      · simp only [whilePop3Exec, id_eq, ↓reduceIte, List.dropWhile_cons, List.takeWhile_cons,
          List.length_cons, List.replicate_succ]
        rw [ih (false :: pref) _ (by simp [hxt]) (by simp [hxt.symm, htp])]
        split
        · funext j; by_cases h1 : j = tmp <;> by_cases h2 : j = x <;>
            simp_all [List.cons_append, List.append_assoc, replicate_append_cons]
        · funext j; by_cases h1 : j = tmp <;> by_cases h2 : j = x <;>
            simp_all [List.cons_append, List.append_assoc, replicate_append_cons]
  have hinc : ∀ l : List Bool,
      (if l.dropWhile id = [] then (List.replicate l.length false).reverse ++ []
       else (true :: List.replicate (l.takeWhile id).length false).reverse ++ (l.dropWhile id).tail) =
        incFixedBits l := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih =>
      cases b
      · simp [incFixedBits]
      · simp only [incFixedBits, List.dropWhile_cons, id_eq, ↓reduceIte, List.length_cons,
          List.takeWhile_cons, List.replicate_succ]
        rw [← ih]
        split
        · simp only [List.reverse_cons, List.reverse_replicate, List.append_nil]
          simpa using replicate_append_cons false [] l.length
        · simp only [List.reverse_cons, List.reverse_replicate, List.append_assoc, List.singleton_append,
            List.cons_append]
          exact replicate_append_cons _ _ _
  simp only [incFixedExec]
  rw [key (S x) [] S rfl ht]
  split
  · rename_i hd
    funext j; simp only [revMoveExec, List.append_nil]
    by_cases h1 : j = x <;> by_cases h2 : j = tmp
    · exact absurd (h1.symm.trans h2) hxt
    · subst h1; simp only [Function.update_self, Function.update_of_ne hxt, Function.update_of_ne h2]
      have := hinc (S j); rw [if_pos hd] at this; exact this
    · subst h2; simp [hxt.symm, ht]
    · simp [h1, h2]
  · rename_i hd
    funext j; simp only [revMoveExec, List.append_nil]
    by_cases h1 : j = x <;> by_cases h2 : j = tmp
    · exact absurd (h1.symm.trans h2) hxt
    · subst h1; simp only [Function.update_self, Function.update_of_ne hxt, Function.update_of_ne h2]
      have := hinc (S j); rw [if_neg hd] at this; exact this
    · subst h2; simp [hxt.symm, ht]
    · simp [h1, h2]

theorem psb_incFixed {K : Type} [DecidableEq K] {x tmp : K} (hxt : x ≠ tmp) :
    PureSB (incFixedExec x tmp) (fun S => 5 * (S x).length + 3 * (S tmp).length + 7) := by
  have hw := psb_whilePop3 x id (psb_push tmp false) (psb_push tmp true) psb_noop
    (indep_push hxt.symm false)
  have hfull := psb_seq hw (psb_revMove hxt.symm)
  refine psb_mono hfull ?_
  intro S
  have h1 : ∀ (l : List Bool) (T : K → List Bool),
      whilePop3Cost x id (fun U => Function.update U tmp (false :: U tmp))
        (fun _ => 1) (fun _ => 1) (fun _ => 1) l T ≤ 2 * l.length + 3 ∧
      ((whilePop3Exec x id (fun U => Function.update U tmp (false :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp))
        id l T) tmp).length ≤ l.length + (T tmp).length + 1 := by
    intro l
    induction l with
    | nil =>
      intro T
      simp only [whilePop3Cost, whilePop3Exec, id_eq, Function.update_of_ne hxt.symm, List.length_nil]
      exact ⟨by omega, by omega⟩
    | cons b l ih =>
      intro T
      cases b
      · simp only [whilePop3Cost, whilePop3Exec, id_eq, Bool.false_eq_true, ↓reduceIte,
          Function.update_self, Function.update_of_ne hxt.symm, List.length_cons]
        exact ⟨by omega, by omega⟩
      · simp only [whilePop3Cost, whilePop3Exec, id_eq, ↓reduceIte, List.length_cons,
          Function.update_of_ne hxt.symm]
        have hih := ih (Function.update (Function.update T x l) tmp (false :: T tmp))
        simp only [Function.update_self, List.length_cons] at hih
        exact ⟨by have := hih.1; omega, by have := hih.2; omega⟩
  have := h1 (S x) S
  omega

theorem indep_incFixed {K : Type} [DecidableEq K] {k x tmp : K} (hx : x ≠ k) (ht : tmp ≠ k) :
    Indep k (incFixedExec x tmp) := by
  intro S l
  simp only [incFixedExec]
  have key : ∀ (m : List Bool) (T : K → List Bool),
      whilePop3Exec x id (fun U => Function.update U tmp (false :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp)) id m (Function.update T k l) =
      Function.update (whilePop3Exec x id (fun U => Function.update U tmp (false :: U tmp))
        (fun U => Function.update U tmp (true :: U tmp)) id m T) k l := by
    intro m
    induction m with
    | nil =>
      intro T; funext j; simp only [whilePop3Exec, id_eq]
      by_cases h1 : j = k <;> by_cases h2 : j = x <;> simp_all
    | cons b m ih =>
      intro T; cases b
      · funext j; simp only [whilePop3Exec, id_eq, Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : j = k <;> by_cases h2 : j = tmp <;> by_cases h3 : j = x <;> simp_all
      · simp only [whilePop3Exec, id_eq, ↓reduceIte]
        have hstep : Function.update (Function.update (Function.update T k l) x m) tmp
            (false :: Function.update (Function.update T k l) x m tmp) =
            Function.update (Function.update (Function.update T x m) tmp
              (false :: Function.update T x m tmp)) k l := by
          funext j; by_cases h1 : j = k <;> by_cases h2 : j = tmp <;> by_cases h3 : j = x <;> simp_all
        rw [hstep, ih]
  rw [Function.update_of_ne hx, key (S x) S, indep_revMove ht hx]

def stripFalseExec {K : Type} [DecidableEq K] (d : K) (S : K → List Bool) : K → List Bool :=
  whilePop3Exec d (fun b => !b) id (fun T => Function.update T d (true :: T d)) id (S d) S

theorem stripFalseExec_eq {K : Type} [DecidableEq K] (d : K) (S : K → List Bool) :
    stripFalseExec d S = Function.update S d ((S d).dropWhile (fun b => !b)) := by
  have key : ∀ (l : List Bool) (T : K → List Bool),
      whilePop3Exec d (fun b => !b) id (fun U => Function.update U d (true :: U d)) id l T =
        Function.update T d (l.dropWhile (fun b => !b)) := by
    intro l
    induction l with
    | nil => intro T; simp [whilePop3Exec]
    | cons b l ih =>
      intro T; cases b
      · simp only [whilePop3Exec, Bool.not_false, ↓reduceIte, id_eq, List.dropWhile_cons]
        rw [ih, Function.update_idem]
      · simp only [whilePop3Exec, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          Function.update_self, Function.update_idem, List.dropWhile_cons]
  exact key (S d) S

theorem psb_stripFalse {K : Type} [DecidableEq K] (d : K) :
    PureSB (stripFalseExec d) (fun S => 2 * (S d).length + 3) := by
  have hw := psb_whilePop3 d (fun b => !b) psb_noop (psb_push d true) psb_noop (indep_id d)
  refine psb_mono hw ?_
  intro S
  have key : ∀ (l : List Bool) (T : K → List Bool),
      whilePop3Cost d (fun b => !b) id (fun _ => 1) (fun _ => 1) (fun _ => 1) l T ≤ 2 * l.length + 3 := by
    intro l
    induction l with
    | nil => intro _; simp [whilePop3Cost]
    | cons b l ih =>
      intro T; cases b
      · simp only [whilePop3Cost, Bool.not_false, ↓reduceIte, id_eq, List.length_cons]
        have := ih (Function.update T d l); omega
      · simp only [whilePop3Cost, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        omega
  exact key (S d) S

theorem indep_stripFalse {K : Type} [DecidableEq K] {k d : K} (hd : d ≠ k) :
    Indep k (stripFalseExec d) := by
  intro S l; funext j; rw [stripFalseExec_eq, stripFalseExec_eq]
  by_cases h1 : j = k <;> by_cases h2 : j = d <;> simp_all

def parseHeaderExec {K : Type} [DecidableEq K] (inp N : K) (S : K → List Bool) : K → List Bool :=
  whilePop3Exec inp id (fun T => Function.update T N (true :: T N)) id id (S inp) S

theorem parseHeaderExec_eq {K : Type} [DecidableEq K] {inp N : K} (hne : inp ≠ N)
    (S : K → List Bool) :
    parseHeaderExec inp N S =
      Function.update (Function.update S inp ((S inp).dropWhile id).tail) N
        (List.replicate (S inp |>.takeWhile id).length true ++ S N) := by
  have key : ∀ (l : List Bool) (T : K → List Bool),
      whilePop3Exec inp id (fun U => Function.update U N (true :: U N)) id id l T =
        Function.update (Function.update T inp (l.dropWhile id).tail) N
          (List.replicate (l.takeWhile id).length true ++ T N) := by
    intro l
    induction l with
    | nil =>
      intro T; funext j
      simp only [whilePop3Exec, id_eq, List.dropWhile_nil, List.tail_nil, List.takeWhile_nil,
        List.length_nil, List.replicate_zero, List.nil_append]
      by_cases h1 : j = N <;> by_cases h2 : j = inp <;> simp_all
    | cons b l ih =>
      intro T; cases b
      · funext j; simp only [whilePop3Exec, id_eq, Bool.false_eq_true, ↓reduceIte,
          List.dropWhile_cons, List.tail_cons, List.takeWhile_cons, List.length_nil,
          List.replicate_zero, List.nil_append]
        by_cases h1 : j = N <;> by_cases h2 : j = inp <;> simp_all
      · simp only [whilePop3Exec, id_eq, ↓reduceIte, List.dropWhile_cons, List.takeWhile_cons,
          List.length_cons, List.replicate_succ]
        rw [ih]
        funext j; by_cases h1 : j = N <;> by_cases h2 : j = inp <;>
          simp_all [replicate_append_cons]
  exact key (S inp) S

theorem psb_parseHeader {K : Type} [DecidableEq K] {inp N : K} (hne : inp ≠ N) :
    PureSB (parseHeaderExec inp N) (fun S => 2 * (S inp).length + 3) := by
  have hw := psb_whilePop3 inp id (psb_push N true) psb_noop psb_noop (indep_push hne.symm true)
  refine psb_mono hw ?_
  intro S
  have key : ∀ (l : List Bool) (T : K → List Bool),
      whilePop3Cost inp id (fun U => Function.update U N (true :: U N))
        (fun _ => 1) (fun _ => 1) (fun _ => 1) l T ≤ 2 * l.length + 3 := by
    intro l
    induction l with
    | nil => intro _; simp [whilePop3Cost]
    | cons b l ih =>
      intro T; cases b
      · simp only [whilePop3Cost, id_eq, Bool.false_eq_true, ↓reduceIte, List.length_cons]; omega
      · simp only [whilePop3Cost, id_eq, ↓reduceIte, List.length_cons]
        have := ih (Function.update (Function.update T inp l) N (true :: (Function.update T inp l) N))
        omega
  exact key (S inp) S

end PEqualNP.Outside.L_meta_32063.Sim


namespace PEqualNP.Outside.L_meta_32063.ReadM

open PEqualNP.Outside.L_meta_32063.Sim

def ofBits : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * ofBits l

theorem ofBits_lt_two_pow : ∀ l : List Bool, ofBits l < 2 ^ l.length
  | [] => by decide
  | b :: l => by
    have ih := ofBits_lt_two_pow l
    simp only [ofBits, List.length_cons, pow_succ']
    cases b <;> simp <;> omega

theorem ofBits_bits (m : ℕ) : ofBits m.bits = m := by
  induction m using Nat.binaryRec with
  | zero => rfl
  | bit b m ih =>
    by_cases h : m = 0 ∧ b = false
    · rcases h with ⟨rfl, rfl⟩; rfl
    · have hcond : m = 0 → b = true := by
        intro hm; cases b; exact absurd ⟨hm, rfl⟩ h; rfl
      rw [Nat.bits_append_bit m b hcond, ofBits, ih, Nat.bit_val]
      cases b <;> simp <;> omega

theorem incBits_bits (m : ℕ) : incBits m.bits = (m + 1).bits := by
  induction m using Nat.binaryRec with
  | zero => rfl
  | bit b m ih =>
    cases b
    · by_cases hm : m = 0
      · subst hm; rfl
      · rw [Nat.bits_append_bit m false (fun h => absurd h hm), incBits]
        have h1 : Nat.bit false m + 1 = Nat.bit true m := by
          rw [Nat.bit_val, Nat.bit_val]; simp
        rw [h1, Nat.bits_append_bit m true (fun _ => rfl)]
    · rw [Nat.bits_append_bit m true (fun _ => rfl), incBits, ih]
      have h1 : Nat.bit true m + 1 = Nat.bit false (m + 1) := by
        rw [Nat.bit_val, Nat.bit_val]; simp; omega
      rw [h1, Nat.bits_append_bit (m + 1) false (fun h => absurd h (Nat.succ_ne_zero m))]

theorem incBits_iter (m : ℕ) : incBits^[m] [] = m.bits := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, incBits_bits]

theorem incBits_length_le : ∀ l : List Bool, (incBits l).length ≤ l.length + 1
  | [] => by decide
  | false :: l => by simp [incBits]
  | true :: l => by
    have ih := incBits_length_le l
    simp only [incBits, List.length_cons]
    omega

theorem bits_length_eq_log2 : ∀ m : ℕ, 0 < m → m.bits.length = m.log2 + 1 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    by_cases h1 : m = 1
    · subst h1; decide
    · have h2 : 2 ≤ m := by omega
      have hdiv : 0 < m / 2 := by omega
      have hlt : m / 2 < m := Nat.div_lt_self hm (by decide)
      have heq : m = Nat.bit (decide (m % 2 = 1)) (m / 2) := by
        rw [Nat.bit_val]
        cases hmod : decide (m % 2 = 1)
        · simp at hmod ⊢; omega
        · simp at hmod ⊢; omega
      have hbits : m.bits = decide (m % 2 = 1) :: (m / 2).bits := by
        conv_lhs => rw [heq]
        exact Nat.bits_append_bit (m / 2) _ (fun h => absurd h (by omega))
      rw [hbits, List.length_cons, ih (m / 2) hlt hdiv, Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      have hlog : Nat.log 2 m = Nat.log 2 (m / 2) + 1 := by
        rw [Nat.log_of_one_lt_of_le (by decide : 1 < 2) h2]
      omega

theorem bits_length_le : ∀ m : ℕ, m.bits.length ≤ m := by
  intro m
  by_cases hm : m = 0
  · subst hm; decide
  · rw [bits_length_eq_log2 m (by omega)]
    have h1 : m.log2 < m := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_lt_self 2 (by omega)
    omega

theorem bits_length_mono {a b : ℕ} (h : a ≤ b) : a.bits.length ≤ b.bits.length := by
  by_cases ha : a = 0
  · subst ha; exact Nat.zero_le _
  · rw [bits_length_eq_log2 a (by omega), bits_length_eq_log2 b (by omega),
        Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (Nat.log_mono_right h) 1

theorem bits_length_le_of_lt_pow {x i : ℕ} (hx : x < 2 ^ i) : x.bits.length ≤ i := by
  by_cases h0 : x = 0
  · subst h0; exact Nat.zero_le _
  · rw [bits_length_eq_log2 x (by omega), Nat.log2_eq_log_two]
    have hlt : Nat.log 2 x < i := Nat.log_lt_of_lt_pow h0 hx
    omega

theorem fib_lt_two_pow : ∀ i : ℕ, Nat.fib i < 2 ^ i
  | 0 => by decide
  | 1 => by decide
  | i + 2 => by
    have h1 := fib_lt_two_pow i
    have h2 := fib_lt_two_pow (i + 1)
    rw [Nat.fib_add_two]
    have hp1 : 2 ^ (i + 2) = 2 * 2 ^ (i + 1) := by rw [pow_succ']
    have hp2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ']
    omega

theorem fib_bits_length_le (i : ℕ) : (Nat.fib i).bits.length ≤ i :=
  bits_length_le_of_lt_pow (fib_lt_two_pow i)

theorem bits_ge_two_pow {m : ℕ} (hm : 0 < m) : 2 ^ (m.bits.length - 1) ≤ m := by
  rw [bits_length_eq_log2 m hm, Nat.add_sub_cancel, Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 (by omega)

theorem dropWhile_not_reverse (l : List Bool) :
    (l.reverse.dropWhile (fun b => !b)).reverse = (ofBits l).bits := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.reverse_cons, ofBits]
    have hcase : ∀ (r : List Bool),
        (r ++ [b]).dropWhile (fun x => !x) =
          if r.dropWhile (fun x => !x) = [] then [b].dropWhile (fun x => !x)
          else r.dropWhile (fun x => !x) ++ [b] := by
      intro r
      induction r with
      | nil => simp
      | cons a r ihr =>
        cases a
        · simp [ihr]
        · simp
    rw [hcase]
    split
    · rename_i hnil
      have h0 : ofBits l = 0 := by
        have := congrArg List.reverse hnil
        simp only [List.reverse_nil] at this
        rw [ih] at this
        have := congrArg ofBits this
        rw [ofBits_bits] at this
        exact this
      rw [h0]
      cases b <;> rfl
    · rename_i hne
      have hpos : ofBits l ≠ 0 := by
        intro h0
        apply hne
        have := congrArg List.reverse ih
        rw [List.reverse_reverse, h0] at this
        exact this
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append, ih]
      have hbit : b.toNat + 2 * ofBits l = Nat.bit b (ofBits l) := by
        rw [Nat.bit_val]; cases b <;> simp <;> omega
      rw [hbit, Nat.bits_append_bit (ofBits l) b (fun h => absurd h hpos)]

def fullAddSum (a b c : Bool) : Bool := xor (xor a b) c
def fullAddCarry (a b c : Bool) : Bool := (a && b) || (c && (a || b))

theorem fullAdd_arith (a b c : Bool) :
    (fullAddSum a b c).toNat + 2 * (fullAddCarry a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

def addBitsAux : List Bool → List Bool → Bool → List Bool
  | [], [], c => if c then [true] else []
  | [], b :: lb, c => fullAddSum false b c :: addBitsAux [] lb (fullAddCarry false b c)
  | a :: la, [], c => fullAddSum a false c :: addBitsAux la [] (fullAddCarry a false c)
  | a :: la, b :: lb, c => fullAddSum a b c :: addBitsAux la lb (fullAddCarry a b c)

theorem ofBits_addBitsAux : ∀ (lb la : List Bool) (c : Bool),
    ofBits (addBitsAux la lb c) = ofBits la + ofBits lb + c.toNat := by
  intro lb
  induction lb with
  | nil =>
    intro la c
    induction la generalizing c with
    | nil => cases c <;> simp [addBitsAux, ofBits]
    | cons a la ih =>
      simp only [addBitsAux, ofBits, ih]
      have := fullAdd_arith a false c
      simp at this
      omega
  | cons b lb ih =>
    intro la c
    cases la with
    | nil =>
      simp only [addBitsAux, ofBits, ih]
      have := fullAdd_arith false b c
      simp at this
      omega
    | cons a la =>
      simp only [addBitsAux, ofBits, ih]
      have := fullAdd_arith a b c
      omega

theorem addBitsAux_len_le : ∀ (lb la : List Bool) (c : Bool),
    la.length ≤ lb.length → (addBitsAux la lb c).length ≤ lb.length + 1 := by
  intro lb
  induction lb with
  | nil =>
    intro la c hle
    cases la with
    | nil => cases c <;> simp [addBitsAux]
    | cons _ _ => simp at hle
  | cons b lb ih =>
    intro la c hle
    cases la with
    | nil =>
      have := ih [] (fullAddCarry false b c) (Nat.zero_le _)
      simp only [addBitsAux, List.length_cons]; omega
    | cons a la =>
      simp only [List.length_cons] at hle
      have := ih la (fullAddCarry a b c) (by omega)
      simp only [addBitsAux, List.length_cons]; omega

def fullSubDiff (a b bor : Bool) : Bool := xor (xor a b) bor
def fullSubBor (a b bor : Bool) : Bool := (!a && (b || bor)) || (b && bor)

theorem fullSub_arith (a b bor : Bool) :
    (fullSubDiff a b bor).toNat + b.toNat + bor.toNat =
      a.toNat + 2 * (fullSubBor a b bor).toNat := by
  cases a <;> cases b <;> cases bor <;> decide

def subBitsAux : List Bool → List Bool → Bool → List Bool × Bool
  | [], _, bor => ([], bor)
  | a :: la, [], bor =>
    let r := subBitsAux la [] (fullSubBor a false bor)
    (fullSubDiff a false bor :: r.1, r.2)
  | a :: la, b :: lb, bor =>
    let r := subBitsAux la lb (fullSubBor a b bor)
    (fullSubDiff a b bor :: r.1, r.2)

theorem subBitsAux_spec : ∀ (la lb : List Bool) (bor : Bool),
    lb.length ≤ la.length →
    (subBitsAux la lb bor).1.length = la.length ∧
    ofBits (subBitsAux la lb bor).1 + ofBits lb + bor.toNat =
      ofBits la + 2 ^ la.length * (subBitsAux la lb bor).2.toNat := by
  intro la
  induction la with
  | nil =>
    intro lb bor hle
    cases lb with
    | nil => cases bor <;> simp [subBitsAux, ofBits]
    | cons _ _ => simp at hle
  | cons a la ih =>
    intro lb bor hle
    cases lb with
    | nil =>
      have h1 := ih [] (fullSubBor a false bor) (Nat.zero_le _)
      simp only [subBitsAux, List.length_cons, ofBits, pow_succ']
      have ha := fullSub_arith a false bor
      simp at ha
      refine ⟨congrArg Nat.succ h1.1, ?_⟩
      have h12 := h1.2
      simp only [ofBits] at h12
      have hpow : 2 * 2 ^ la.length * (subBitsAux la [] (fullSubBor a false bor)).2.toNat =
          2 * (2 ^ la.length * (subBitsAux la [] (fullSubBor a false bor)).2.toNat) := by ring
      omega
    | cons b lb =>
      simp only [List.length_cons] at hle
      have h1 := ih lb (fullSubBor a b bor) (by omega)
      simp only [subBitsAux, List.length_cons, ofBits, pow_succ']
      have ha := fullSub_arith a b bor
      refine ⟨congrArg Nat.succ h1.1, ?_⟩
      have h12 := h1.2
      have hpow : 2 * 2 ^ la.length * (subBitsAux la lb (fullSubBor a b bor)).2.toNat =
          2 * (2 ^ la.length * (subBitsAux la lb (fullSubBor a b bor)).2.toNat) := by ring
      omega

abbrev RK := Fin 15
abbrev rIn    : RK := 0
abbrev rOut   : RK := 1
abbrev rN     : RK := 2
abbrev rV     : RK := 3
abbrev rT     : RK := 4
abbrev rL     : RK := 5
abbrev rF0    : RK := 6
abbrev rF1    : RK := 7
abbrev rRem   : RK := 8
abbrev rRrev  : RK := 9
abbrev rDiff  : RK := 10
abbrev rTmp1  : RK := 11
abbrev rTmp2  : RK := 12
abbrev rCarry : RK := 13
abbrev rUnder : RK := 14

def doubleNExec (S : RK → List Bool) : RK → List Bool :=
  (S rN).foldl (fun T _ => Function.update T rV (true :: true :: T rV)) (Function.update S rN [])

theorem psb_doubleN : PureSB doubleNExec (fun S => 4 * (S rN).length + 1) := by
  have hstep : PureSB (fun T : RK → List Bool => Function.update T rV (true :: true :: T rV)) (fun _ => 2) := by
    have h := psb_seq (psb_push rV true) (psb_push rV true)
    refine psb_congr h ?_
    intro T; funext j; by_cases hj : j = rV; · subst hj; simp
    simp [hj]
  have hind : Indep rN (fun T : RK → List Bool => Function.update T rV (true :: true :: T rV)) := by
    intro T l; funext j
    by_cases h1 : j = rN; · subst h1; simp [Fin.ext_iff]
    by_cases h2 : j = rV; · subst h2; simp [Fin.ext_iff]
    simp [h1, h2]
  have h := psb_forEachIgn rN hstep hind
  refine psb_mono h ?_
  intro S
  have hc := forEachCost_le rN (fun _ T => Function.update T rV (true :: true :: T rV))
    (fun _ _ => 2) (fun _ => True) 2 (fun _ _ _ => trivial) (fun _ _ _ => le_rfl)
    (fun _ _ _ => trivial) (S rN) S trivial
  omega

theorem doubleNExec_eq (S : RK → List Bool) :
    doubleNExec S = Function.update (Function.update S rN []) rV (List.replicate (2 * (S rN).length) true ++ S rV) := by
  have key : ∀ (l : List Bool) (T : RK → List Bool),
      l.foldl (fun U _ => Function.update U rV (true :: true :: U rV)) T =
        Function.update T rV (List.replicate (2 * l.length) true ++ T rV) := by
    intro l
    induction l with
    | nil => intro T; simp [Fin.ext_iff, Function.update_eq_self]
    | cons _ l ih =>
      intro T
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      funext j
      by_cases hj : j = rV
      · subst hj
        simp only [Function.update_self]
        rw [show 2 * (l.length + 1) = 2 * l.length + 2 by omega, List.replicate_add]
        simp [List.append_assoc, replicate_append_cons]
      · simp [hj]
  simp only [doubleNExec]
  rw [key, Function.update_of_ne (by decide : rV ≠ rN)]

def computeTExec (S : RK → List Bool) : RK → List Bool :=
  let S1 := incBinExec rT rTmp1 S
  let S2 := copyExec rV rTmp2 rTmp1 S1
  (S2 rTmp2).foldl (fun T _ => incBinExec rT rTmp1 T) (Function.update S2 rTmp2 [])

def computeTCost (S : RK → List Bool) : ℕ :=
  let S1 := incBinExec rT rTmp1 S
  let S2 := copyExec rV rTmp2 rTmp1 S1
  forEachCost rTmp2 (fun _ => incBinExec rT rTmp1)
    (fun _ U => 5 * (U rT).length + 3 * (U rTmp1).length + 7) (S2 rTmp2) S2 +
    ((7 * (S1 rV).length + 4 * (S1 rTmp1).length + 2) +
     (5 * (S rT).length + 3 * (S rTmp1).length + 7))

theorem psb_computeT : PureSB computeTExec computeTCost := by
  unfold computeTExec computeTCost
  have h1 : PureSB (incBinExec rT rTmp1) (fun U => 5 * (U rT).length + 3 * (U rTmp1).length + 7) :=
    psb_incBin (by decide)
  have h2 : PureSB (copyExec rV rTmp2 rTmp1) (fun U => 7 * (U rV).length + 4 * (U rTmp1).length + 2) :=
    psb_copy (by decide) (by decide) (by decide)
  have h3 := psb_forEachIgn rTmp2 h1 (indep_incBin (by decide) (by decide))
  exact psb_seq (psb_seq h1 h2) h3

theorem computeT_spec (S : RK → List Bool) (hT : S rT = []) (h1 : S rTmp1 = []) (h2 : S rTmp2 = []) :
    computeTExec S = Function.update S rT ((S rV).length + 1).bits ∧
    computeTCost S ≤ 5 * ((S rV).length + 1) ^ 2 + 20 * ((S rV).length + 1) + 20 := by
  set v := (S rV).length
  have hS1 : incBinExec rT rTmp1 S = Function.update S rT [true] := by
    rw [incBinExec_of_empty (by decide) S h1, hT]; rfl
  have hS2 : copyExec rV rTmp2 rTmp1 (incBinExec rT rTmp1 S) =
      Function.update (Function.update S rT [true]) rTmp2 (S rV) := by
    rw [hS1, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, h1])]
    funext j
    by_cases hj1 : j = rTmp2; · subst hj1; simp [Fin.ext_iff, h2]
    by_cases hj2 : j = rT; · subst hj2; simp [Fin.ext_iff]
    simp [hj1, hj2]
  have hfold : ∀ (l : List Bool) (m : ℕ) (U : RK → List Bool),
      U rT = m.bits → U rTmp1 = [] →
      l.foldl (fun W _ => incBinExec rT rTmp1 W) U = Function.update U rT (m + l.length).bits ∧
      forEachCost rTmp2 (fun _ => incBinExec rT rTmp1)
        (fun _ W => 5 * (W rT).length + 3 * (W rTmp1).length + 7) l U ≤
        l.length * (5 * (m + l.length) + 9) + 1 := by
    intro l
    induction l with
    | nil =>
      intro m U hUT _
      refine ⟨by simp [hUT, Function.update_eq_self], by simp [forEachCost]⟩
    | cons _ l ih =>
      intro m U hUT hU1
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have hinc : incBinExec rT rTmp1 U = Function.update U rT (m + 1).bits := by
        rw [incBinExec_of_empty (by decide) U hU1, hUT, incBits_bits]
      have hinc' : incBinExec rT rTmp1 (Function.update U rTmp2 l) =
          Function.update (Function.update U rTmp2 l) rT (m + 1).bits := by
        rw [incBinExec_of_empty (by decide) _ (by simp [Fin.ext_iff, hU1]), Function.update_of_ne (by decide),
            hUT, incBits_bits]
      have hres1 := ih (m + 1) (incBinExec rT rTmp1 U) (by rw [hinc]; simp) (by rw [hinc]; simp [Fin.ext_iff, hU1])
      have hres2 := ih (m + 1) (incBinExec rT rTmp1 (Function.update U rTmp2 l))
        (by rw [hinc']; simp) (by rw [hinc']; simp [Fin.ext_iff, hU1])
      refine ⟨?_, ?_⟩
      · rw [hres1.1, hinc, Function.update_idem, show m + 1 + l.length = m + (l.length + 1) by omega]
      · have hlen : (Function.update U rTmp2 l rT).length ≤ m := by
          rw [Function.update_of_ne (by decide), hUT]; exact bits_length_le m
        have hu1' : (Function.update U rTmp2 l rTmp1).length = 0 := by
          rw [Function.update_of_ne (by decide), hU1]; rfl
        have hc2 := hres2.2
        have hm1 : m + 1 + l.length = m + (l.length + 1) := by omega
        rw [hm1] at hc2
        have hmul : (l.length + 1) * (5 * (m + (l.length + 1)) + 9) =
            l.length * (5 * (m + (l.length + 1)) + 9) + (5 * (m + (l.length + 1)) + 9) := by ring
        omega
  have hS2_rTmp2 : (copyExec rV rTmp2 rTmp1 (incBinExec rT rTmp1 S)) rTmp2 = S rV := by
    rw [hS2]; simp
  have hmain := hfold (S rV) 1 (Function.update (copyExec rV rTmp2 rTmp1 (incBinExec rT rTmp1 S)) rTmp2 [])
    (by rw [hS2]; simp [Fin.ext_iff]) (by rw [hS2]; simp [Fin.ext_iff, h1])
  have hmainCost := hfold (S rV) 1 (copyExec rV rTmp2 rTmp1 (incBinExec rT rTmp1 S))
    (by rw [hS2]; simp [Fin.ext_iff]) (by rw [hS2]; simp [Fin.ext_iff, h1])
  refine ⟨?_, ?_⟩
  · simp only [computeTExec]
    rw [hS2_rTmp2, hmain.1, hS2]
    funext j
    by_cases hj1 : j = rT
    · subst hj1; simp [v, Nat.add_comm]
    by_cases hj2 : j = rTmp2
    · subst hj2; simp [Fin.ext_iff, h2]
    simp [hj1, hj2]
  · simp only [computeTCost]
    rw [hS2_rTmp2]
    have hc := hmainCost.2
    have hS1v : (incBinExec rT rTmp1 S rV).length = v := by rw [hS1]; simp [Fin.ext_iff, v]
    have hS1t : (incBinExec rT rTmp1 S rTmp1).length = 0 := by rw [hS1]; simp [Fin.ext_iff, h1]
    have hSt : (S rT).length = 0 := by simp [hT]
    have hS1' : (S rTmp1).length = 0 := by simp [h1]
    rw [hS1v, hS1t, hSt, hS1']
    have hsq : (v + 1) ^ 2 = (v + 1) * (v + 1) := sq (v + 1)
    have hle1 : v * (5 * (1 + v) + 9) ≤ (v + 1) * (5 * (v + 1) + 9) :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith

def push4LExec (S : RK → List Bool) : RK → List Bool :=
  Function.update S rL (true :: true :: true :: true :: S rL)

theorem psb_push4L : PureSB push4LExec (fun _ => 4) := by
  have h1 := psb_seq (psb_push rL true) (psb_push rL true)
  have h2 := psb_seq h1 h1
  refine psb_congr h2 ?_
  intro S; funext j; by_cases hj : j = rL; · subst hj; simp [push4LExec]
  simp [push4LExec, hj]

def copyT2Exec (S : RK → List Bool) : RK → List Bool :=
  copyExec rT rL rTmp1 (copyExec rT rL rTmp1 S)

def copyT2Cost (S : RK → List Bool) : ℕ :=
  (7 * (copyExec rT rL rTmp1 S rT).length + 4 * (copyExec rT rL rTmp1 S rTmp1).length + 2) +
    (7 * (S rT).length + 4 * (S rTmp1).length + 2)

theorem psb_copyT2 : PureSB copyT2Exec copyT2Cost := by
  unfold copyT2Exec copyT2Cost
  exact psb_seq (psb_copy (a := rT) (b := rL) (tmp := rTmp1) (by decide) (by decide) (by decide))
                (psb_copy (a := rT) (b := rL) (tmp := rTmp1) (by decide) (by decide) (by decide))

theorem indep_copyT2 : Indep rV copyT2Exec := by
  unfold copyT2Exec
  exact indep_seq (indep_copy (a := rT) (b := rL) (tmp := rTmp1) (by decide) (by decide) (by decide))
                  (indep_copy (a := rT) (b := rL) (tmp := rTmp1) (by decide) (by decide) (by decide))

def computeLExec (S : RK → List Bool) : RK → List Bool :=
  let S1 := push4LExec S
  let S2 := (S1 rV).foldl (fun U _ => copyT2Exec U) (Function.update S1 rV [])
  clearExec rT S2

def computeLCost (S : RK → List Bool) : ℕ :=
  let S1 := push4LExec S
  let S2 := (S1 rV).foldl (fun U _ => copyT2Exec U) (Function.update S1 rV [])
  (3 * (S2 rT).length + 1) +
    (forEachCost rV (fun _ => copyT2Exec) (fun _ => copyT2Cost) (S1 rV) S1 + 4)

theorem psb_computeL : PureSB computeLExec computeLCost := by
  unfold computeLExec computeLCost
  exact psb_seq (psb_seq psb_push4L (psb_forEachIgn rV psb_copyT2 indep_copyT2))
    (psb_clear rT)

theorem computeL_spec (S : RK → List Bool) (hL : S rL = []) (h1 : S rTmp1 = []) :
    ∃ lL : List Bool, lL.length = 2 * (S rV).length * (S rT).length + 4 ∧
      computeLExec S = Function.update (Function.update (Function.update S rV []) rT []) rL lL ∧
      computeLCost S ≤ 16 * (S rV).length * (S rT).length + 6 * (S rV).length + 3 * (S rT).length + 6 := by
  have hcopy2 : ∀ (U : RK → List Bool), U rTmp1 = [] →
      copyT2Exec U = Function.update U rL (U rT ++ U rT ++ U rL) ∧
      copyT2Cost U ≤ 14 * (U rT).length + 4 := by
    intro U hU1
    have hc1 : copyExec rT rL rTmp1 U = Function.update U rL (U rT ++ U rL) :=
      copyExec_of_empty (by decide) (by decide) (by decide) U hU1
    have hc2 : copyExec rT rL rTmp1 (copyExec rT rL rTmp1 U) =
        Function.update U rL (U rT ++ U rT ++ U rL) := by
      rw [hc1, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, hU1])]
      funext j; by_cases hj : j = rL; · subst hj; simp [Fin.ext_iff, List.append_assoc]
      simp [hj]
    refine ⟨hc2, ?_⟩
    simp only [copyT2Cost, hc1, Function.update_of_ne (by decide : rT ≠ rL),
      Function.update_of_ne (by decide : rTmp1 ≠ rL), hU1, List.length_nil]
    omega
  have hfold : ∀ (l : List Bool) (U : RK → List Bool), U rTmp1 = [] →
      ∃ lL : List Bool, lL.length = 2 * l.length * (U rT).length + (U rL).length ∧
        l.foldl (fun W _ => copyT2Exec W) U = Function.update U rL lL ∧
        forEachCost rV (fun _ => copyT2Exec) (fun _ => copyT2Cost) l U ≤
          l.length * (14 * (U rT).length + 6) + 1 := by
    intro l
    induction l with
    | nil =>
      intro U _
      exact ⟨U rL, by simp, by simp [Function.update_eq_self], by simp [forEachCost]⟩
    | cons _ l ih =>
      intro U hU1
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have h1 := hcopy2 U hU1
      have h1' := hcopy2 (Function.update U rV l) (by simp [Fin.ext_iff, hU1])
      obtain ⟨lL, hlL, hfe, _⟩ := ih (copyT2Exec U) (by rw [h1.1]; simp [Fin.ext_iff, hU1])
      obtain ⟨_, _, _, hfc⟩ := ih (copyT2Exec (Function.update U rV l)) (by rw [h1'.1]; simp [Fin.ext_iff, hU1])
      refine ⟨lL, ?_, ?_, ?_⟩
      · rw [hlL, h1.1]; simp only [Function.update_self, Function.update_of_ne (by decide : rT ≠ rL),
          List.length_append]
        have hmul : 2 * (l.length + 1) * (U rT).length = 2 * l.length * (U rT).length + 2 * (U rT).length := by ring
        omega
      · rw [hfe, h1.1, Function.update_idem]
      · have hT1 : (copyT2Exec (Function.update U rV l) rT).length = (U rT).length := by
          rw [h1'.1]; simp [Fin.ext_iff]
        rw [hT1] at hfc
        have hc2 := h1'.2
        simp only [Function.update_of_ne (by decide : rT ≠ rV)] at hc2
        have hmul : (l.length + 1) * (14 * (U rT).length + 6) =
            l.length * (14 * (U rT).length + 6) + (14 * (U rT).length + 6) := by ring
        omega
  have hS1rV : (push4LExec S) rV = S rV := by simp [Fin.ext_iff, push4LExec]
  obtain ⟨lL, hlL, hfe, _⟩ := hfold (S rV) (Function.update (push4LExec S) rV []) (by simp [Fin.ext_iff, push4LExec, h1])
  obtain ⟨_, _, _, hfc⟩ := hfold (S rV) (push4LExec S) (by simp [Fin.ext_iff, push4LExec, h1])
  refine ⟨lL, ?_, ?_, ?_⟩
  · rw [hlL]; simp [Fin.ext_iff, push4LExec, hL]
  · simp only [computeLExec, hS1rV, hfe, clearExec]
    funext j
    by_cases h1 : j = rT; · subst h1; simp [Fin.ext_iff]
    by_cases h2 : j = rL; · subst h2; simp [Fin.ext_iff]
    by_cases h3 : j = rV; · subst h3; simp [Fin.ext_iff]
    simp [Fin.ext_iff, push4LExec, h1, h2, h3]
  · simp only [computeLCost, hS1rV, hfe]
    have hT1 : (push4LExec S rT).length = (S rT).length := by simp [Fin.ext_iff, push4LExec]
    rw [hT1] at hfc
    have hT2 : (Function.update (Function.update (push4LExec S) rV []) rL lL rT).length = (S rT).length := by
      simp [Fin.ext_iff, push4LExec]
    rw [hT2]
    have hmul : (S rV).length * (14 * (S rT).length + 6) =
        14 * (S rV).length * (S rT).length + 6 * (S rV).length := by ring
    have hmul2 : 14 * (S rV).length * (S rT).length ≤ 16 * (S rV).length * (S rT).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

def addBitStep (b1 b0 c : Bool) (S : RK → List Bool) : RK → List Bool :=
  let S1 := Function.update S rTmp2 (fullAddSum b0 b1 c :: S rTmp2)
  if fullAddCarry b0 b1 c then Function.update S1 rCarry (true :: S1 rCarry) else S1

theorem psb_addBitStep (b1 b0 c : Bool) : PureSB (addBitStep b1 b0 c) (fun _ => 2) := by
  have hpush := psb_push rTmp2 (fullAddSum b0 b1 c)
  cases hc : fullAddCarry b0 b1 c
  · exact psb_congr (psb_seq hpush psb_noop) (fun S => by simp [addBitStep, hc])
  · exact psb_congr (psb_seq hpush (psb_push rCarry true)) (fun S => by simp [addBitStep, hc])

def fibInnerStep (b1 : Bool) (S : RK → List Bool) : RK → List Bool :=
  let S1 := Function.update S rTmp1 (b1 :: S rTmp1)
  match S1 rF0 with
  | [] =>
    let S2 := Function.update S1 rF0 []
    match S2 rCarry with
    | [] => addBitStep b1 false false (Function.update S2 rCarry [])
    | false :: l => addBitStep b1 false false (Function.update S2 rCarry l)
    | true :: l => addBitStep b1 false true (Function.update S2 rCarry l)
  | false :: l0 =>
    let S2 := Function.update S1 rF0 l0
    match S2 rCarry with
    | [] => addBitStep b1 false false (Function.update S2 rCarry [])
    | false :: l => addBitStep b1 false false (Function.update S2 rCarry l)
    | true :: l => addBitStep b1 false true (Function.update S2 rCarry l)
  | true :: l0 =>
    let S2 := Function.update S1 rF0 l0
    match S2 rCarry with
    | [] => addBitStep b1 true false (Function.update S2 rCarry [])
    | false :: l => addBitStep b1 true false (Function.update S2 rCarry l)
    | true :: l => addBitStep b1 true true (Function.update S2 rCarry l)

theorem psb_fibInnerStep (b1 : Bool) : PureSB (fibInnerStep b1) (fun _ => 9) := by
  unfold fibInnerStep
  have hcarry : ∀ b0 : Bool, PureSB (fun S2 : RK → List Bool =>
      match S2 rCarry with
      | [] => addBitStep b1 b0 false (Function.update S2 rCarry [])
      | false :: l => addBitStep b1 b0 false (Function.update S2 rCarry l)
      | true :: l => addBitStep b1 b0 true (Function.update S2 rCarry l)) (fun _ => 5) := fun b0 => by
    refine psb_mono (psb_branchPop rCarry (psb_addBitStep b1 b0 false) (psb_addBitStep b1 b0 false)
      (psb_addBitStep b1 b0 true)) ?_
    intro S2; cases S2 rCarry with | nil => simp | cons b _ => cases b <;> simp
  have hf0 := psb_branchPop rF0 (hcarry false) (hcarry false) (hcarry true)
  have hf0' : PureSB _ (fun _ => 8) := psb_mono hf0 (fun S1 => by
    cases S1 rF0 with | nil => simp | cons b _ => cases b <;> simp)
  exact psb_seq (psb_push rTmp1 b1) hf0'

theorem indep_fibInnerStep (b1 : Bool) : Indep rF1 (fibInnerStep b1) := by
  intro S l
  simp only [fibInnerStep]
  have h1 : Function.update (Function.update S rF1 l) rTmp1 (b1 :: Function.update S rF1 l rTmp1) =
      Function.update (Function.update S rTmp1 (b1 :: S rTmp1)) rF1 l := by
    funext j
    by_cases h1 : j = rF1; · subst h1; simp [Fin.ext_iff]
    by_cases h2 : j = rTmp1; · subst h2; simp [Fin.ext_iff]
    simp [h1, h2]
  rw [h1, Function.update_of_ne (by decide : rF0 ≠ rF1)]
  have hadd : ∀ b0 c (U : RK → List Bool),
      addBitStep b1 b0 c (Function.update U rF1 l) = Function.update (addBitStep b1 b0 c U) rF1 l := by
    intro b0 c U; funext j; simp only [addBitStep]
    cases fullAddCarry b0 b1 c
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : j = rF1; · subst h1; simp [Fin.ext_iff]
      by_cases h2 : j = rTmp2; · subst h2; simp [Fin.ext_iff]
      simp [h1, h2]
    · simp only [↓reduceIte]
      by_cases h1 : j = rF1; · subst h1; simp [Fin.ext_iff]
      by_cases h2 : j = rCarry; · subst h2; simp [Fin.ext_iff]
      by_cases h3 : j = rTmp2; · subst h3; simp [Fin.ext_iff]
      simp [h1, h2, h3]
  have hcar : ∀ b0 (U : RK → List Bool),
      (match Function.update U rF1 l rCarry with
       | [] => addBitStep b1 b0 false (Function.update (Function.update U rF1 l) rCarry [])
       | false :: l' => addBitStep b1 b0 false (Function.update (Function.update U rF1 l) rCarry l')
       | true :: l' => addBitStep b1 b0 true (Function.update (Function.update U rF1 l) rCarry l')) =
      Function.update (match U rCarry with
       | [] => addBitStep b1 b0 false (Function.update U rCarry [])
       | false :: l' => addBitStep b1 b0 false (Function.update U rCarry l')
       | true :: l' => addBitStep b1 b0 true (Function.update U rCarry l')) rF1 l := by
    intro b0 U
    rw [Function.update_of_ne (by decide : rCarry ≠ rF1)]
    cases U rCarry with
    | nil => dsimp only; rw [Function.update_comm (by decide : rF1 ≠ rCarry), hadd]
    | cons b l' => cases b <;> (dsimp only; rw [Function.update_comm (by decide : rF1 ≠ rCarry), hadd])
  cases (Function.update S rTmp1 (b1 :: S rTmp1)) rF0 with
  | nil => dsimp only; rw [Function.update_comm (by decide : rF1 ≠ rF0)]; exact hcar false _
  | cons b l0 =>
    cases b
    · dsimp only; rw [Function.update_comm (by decide : rF1 ≠ rF0)]; exact hcar false _
    · dsimp only; rw [Function.update_comm (by decide : rF1 ≠ rF0)]; exact hcar true _

def fibFinishCarry (S : RK → List Bool) : RK → List Bool :=
  match S rCarry with
  | [] => Function.update S rCarry []
  | false :: l => Function.update S rCarry l
  | true :: l => Function.update (Function.update S rCarry l) rTmp2 (true :: (Function.update S rCarry l) rTmp2)

theorem psb_fibFinishCarry : PureSB fibFinishCarry (fun _ => 4) := by
  unfold fibFinishCarry
  refine psb_mono (psb_branchPop rCarry psb_noop psb_noop (psb_push rTmp2 true)) ?_
  intro S; cases S rCarry with | nil => simp | cons b _ => cases b <;> simp

theorem indep_fibFinishCarry : Indep rL fibFinishCarry := by
  intro S l
  simp only [fibFinishCarry, Function.update_of_ne (by decide : rCarry ≠ rL)]
  cases S rCarry with
  | nil =>
    funext j
    by_cases h1 : j = rL; · subst h1; simp [Fin.ext_iff]
    by_cases h2 : j = rCarry; · subst h2; simp [Fin.ext_iff]
    simp [h1, h2]
  | cons b lr =>
    cases b
    · funext j
      by_cases h1 : j = rL; · subst h1; simp [Fin.ext_iff]
      by_cases h2 : j = rCarry; · subst h2; simp [Fin.ext_iff]
      simp [h1, h2]
    · funext j
      by_cases h1 : j = rL; · subst h1; simp [Fin.ext_iff]
      by_cases h2 : j = rCarry; · subst h2; simp [Fin.ext_iff]
      by_cases h3 : j = rTmp2; · subst h3; simp [Fin.ext_iff]
      simp [h1, h2, h3]

def fibStepExec (S : RK → List Bool) : RK → List Bool :=
  let S1 := (S rF1).foldl (fun U b1 => fibInnerStep b1 U) (Function.update S rF1 [])
  let S2 := clearExec rF0 S1
  let S3 := fibFinishCarry S2
  let S4 := stripFalseExec rTmp2 S3
  let S5 := revMoveExec rTmp1 rF0 S4
  revMoveExec rTmp2 rF1 S5

def fibStepCost (S : RK → List Bool) : ℕ :=
  let S1 := (S rF1).foldl (fun U b1 => fibInnerStep b1 U) (Function.update S rF1 [])
  let S2 := clearExec rF0 S1
  let S3 := fibFinishCarry S2
  let S4 := stripFalseExec rTmp2 S3
  let S5 := revMoveExec rTmp1 rF0 S4
  (3 * (S5 rTmp2).length + 1) +
    ((3 * (S4 rTmp1).length + 1) +
      ((2 * (S3 rTmp2).length + 3) +
        (4 + ((3 * (S1 rF0).length + 1) +
          forEachCost rF1 (fun b1 => fibInnerStep b1) (fun _ _ => 9) (S rF1) S))))

theorem psb_fibStep : PureSB fibStepExec fibStepCost := by
  unfold fibStepExec fibStepCost
  exact psb_seq
    (psb_seq
      (psb_seq
        (psb_seq
          (psb_seq (psb_forEach rF1 (B := fun _ _ => 9) (psb_fibInnerStep false) (psb_fibInnerStep true) indep_fibInnerStep)
            (psb_clear rF0))
          psb_fibFinishCarry)
        (psb_stripFalse rTmp2))
      (psb_revMove (a := rTmp1) (b := rF0) (by decide)))
    (psb_revMove (a := rTmp2) (b := rF1) (by decide))

theorem indep_fibStep : Indep rL fibStepExec := by
  unfold fibStepExec
  have hindInner : ∀ b1, Indep rL (fibInnerStep b1) := by
    intro b1 S l
    simp only [fibInnerStep]
    have h1 : Function.update (Function.update S rL l) rTmp1 (b1 :: Function.update S rL l rTmp1) =
        Function.update (Function.update S rTmp1 (b1 :: S rTmp1)) rL l := by
      funext j
      by_cases h1 : j = rL; · subst h1; simp [Fin.ext_iff]
      by_cases h2 : j = rTmp1; · subst h2; simp [Fin.ext_iff]
      simp [h1, h2]
    rw [h1, Function.update_of_ne (by decide : rF0 ≠ rL)]
    have hadd : ∀ b0 c (U : RK → List Bool),
        addBitStep b1 b0 c (Function.update U rL l) = Function.update (addBitStep b1 b0 c U) rL l := by
      intro b0 c U; funext j; simp only [addBitStep]
      cases fullAddCarry b0 b1 c
      · simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : j = rL; · subst h1; simp [Fin.ext_iff]
        by_cases h2 : j = rTmp2; · subst h2; simp [Fin.ext_iff]
        simp [h1, h2]
      · simp only [↓reduceIte]
        by_cases h1 : j = rL; · subst h1; simp [Fin.ext_iff]
        by_cases h2 : j = rCarry; · subst h2; simp [Fin.ext_iff]
        by_cases h3 : j = rTmp2; · subst h3; simp [Fin.ext_iff]
        simp [h1, h2, h3]
    have hcar : ∀ b0 (U : RK → List Bool),
        (match Function.update U rL l rCarry with
         | [] => addBitStep b1 b0 false (Function.update (Function.update U rL l) rCarry [])
         | false :: l' => addBitStep b1 b0 false (Function.update (Function.update U rL l) rCarry l')
         | true :: l' => addBitStep b1 b0 true (Function.update (Function.update U rL l) rCarry l')) =
        Function.update (match U rCarry with
         | [] => addBitStep b1 b0 false (Function.update U rCarry [])
         | false :: l' => addBitStep b1 b0 false (Function.update U rCarry l')
         | true :: l' => addBitStep b1 b0 true (Function.update U rCarry l')) rL l := by
      intro b0 U
      rw [Function.update_of_ne (by decide : rCarry ≠ rL)]
      cases U rCarry with
      | nil => dsimp only; rw [Function.update_comm (by decide : rL ≠ rCarry), hadd]
      | cons b l' => cases b <;> (dsimp only; rw [Function.update_comm (by decide : rL ≠ rCarry), hadd])
    cases (Function.update S rTmp1 (b1 :: S rTmp1)) rF0 with
    | nil => dsimp only; rw [Function.update_comm (by decide : rL ≠ rF0)]; exact hcar false _
    | cons b l0 =>
      cases b
      · dsimp only; rw [Function.update_comm (by decide : rL ≠ rF0)]; exact hcar false _
      · dsimp only; rw [Function.update_comm (by decide : rL ≠ rF0)]; exact hcar true _
  have hindFold : Indep rL (fun S => (S rF1).foldl (fun U b1 => fibInnerStep b1 U) (Function.update S rF1 [])) := by
    intro S l; dsimp only
    rw [Function.update_of_ne (by decide : rF1 ≠ rL), Function.update_comm (by decide : rL ≠ rF1)]
    generalize S rF1 = lb
    generalize Function.update S rF1 [] = U
    induction lb generalizing U with
    | nil => rfl
    | cons b lb ih => simp only [List.foldl_cons]; rw [hindInner b, ih]
  exact indep_seq (indep_seq (indep_seq (indep_seq (indep_seq hindFold
    (indep_clear (a := rF0) (by decide))) indep_fibFinishCarry) (indep_stripFalse (d := rTmp2) (by decide)))
    (indep_revMove (a := rTmp1) (b := rF0) (by decide) (by decide)))
    (indep_revMove (a := rTmp2) (b := rF1) (by decide) (by decide))

theorem fibStep_spec (S : RK → List Bool) (a b : ℕ) (hab : a ≤ b)
    (hF0 : S rF0 = a.bits) (hF1 : S rF1 = b.bits)
    (h1 : S rTmp1 = []) (h2 : S rTmp2 = []) (hC : S rCarry = []) :
    fibStepExec S = Function.update (Function.update S rF0 b.bits) rF1 (a + b).bits ∧
    fibStepCost S ≤ 22 * b.bits.length + 18 := by
  have hlen : a.bits.length ≤ b.bits.length := bits_length_mono hab
  have hloop : ∀ (lb la : List Bool) (c : Bool) (U : RK → List Bool),
      la.length ≤ lb.length → U rF0 = la → U rCarry = (if c then [true] else []) →
      fibFinishCarry (clearExec rF0 (lb.foldl (fun W b1 => fibInnerStep b1 W) U)) =
        Function.update (Function.update (Function.update (Function.update U rF0 []) rCarry [])
          rTmp1 (lb.reverse ++ U rTmp1)) rTmp2 ((addBitsAux la lb c).reverse ++ U rTmp2) ∧
      ((lb.foldl (fun W b1 => fibInnerStep b1 W) U) rF0).length = 0 := by
    intro lb
    induction lb with
    | nil =>
      intro la c U hle hU0 hUC
      cases la with
      | nil =>
        refine ⟨?_, by simp [hU0]⟩
        funext j
        by_cases j1 : j = rTmp2
        · subst j1; cases c <;> simp [clearExec, fibFinishCarry, addBitsAux, hUC, Fin.ext_iff]
        by_cases j2 : j = rTmp1
        · subst j2; cases c <;> simp [clearExec, fibFinishCarry, addBitsAux, hUC, Fin.ext_iff]
        by_cases j3 : j = rCarry
        · subst j3; cases c <;> simp [clearExec, fibFinishCarry, addBitsAux, hUC, Fin.ext_iff]
        by_cases j4 : j = rF0
        · subst j4; cases c <;> simp [clearExec, fibFinishCarry, addBitsAux, hUC, Fin.ext_iff]
        cases c <;> simp [clearExec, fibFinishCarry, addBitsAux, hUC, j1, j2, j3, j4, Fin.ext_iff]
      | cons _ _ => simp at hle
    | cons b1 lb ih =>
      intro la c U hle hU0 hUC
      simp only [List.foldl_cons]
      have hstep : fibInnerStep b1 U =
          Function.update (Function.update (Function.update (Function.update U rTmp1 (b1 :: U rTmp1))
            rF0 la.tail) rCarry (if fullAddCarry (la.headD false) b1 c then [true] else []))
            rTmp2 (fullAddSum (la.headD false) b1 c :: U rTmp2) := by
        have hadd : ∀ b0 c0 (W : RK → List Bool), W rCarry = [] →
            addBitStep b1 b0 c0 W =
              Function.update (Function.update W rCarry (if fullAddCarry b0 b1 c0 then [true] else []))
                rTmp2 (fullAddSum b0 b1 c0 :: W rTmp2) := by
          intro b0 c0 W hWC
          funext j; simp only [addBitStep]
          by_cases j1 : j = rTmp2
          · subst j1; cases fullAddCarry b0 b1 c0 <;> simp [Fin.ext_iff]
          by_cases j2 : j = rCarry
          · subst j2; cases fullAddCarry b0 b1 c0 <;> simp [hWC, Fin.ext_iff]
          cases fullAddCarry b0 b1 c0 <;> simp [j1, j2, Fin.ext_iff]
        have hmid : ∀ b0 (W : RK → List Bool), W rCarry = (if c then [true] else []) →
            (match W rCarry with
             | [] => addBitStep b1 b0 false (Function.update W rCarry [])
             | false :: l => addBitStep b1 b0 false (Function.update W rCarry l)
             | true :: l => addBitStep b1 b0 true (Function.update W rCarry l)) =
            Function.update (Function.update W rCarry (if fullAddCarry b0 b1 c then [true] else []))
              rTmp2 (fullAddSum b0 b1 c :: W rTmp2) := by
          intro b0 W hWC
          cases c
          · simp only [Bool.false_eq_true, ↓reduceIte] at hWC ⊢
            rw [hWC]; dsimp only
            rw [hadd b0 false _ (by simp)]
            funext j; by_cases j1 : j = rTmp2; · subst j1; simp [Fin.ext_iff]
            by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
            simp [j1, j2]
          · simp only [↓reduceIte] at hWC ⊢
            rw [hWC]; dsimp only
            rw [hadd b0 true _ (by simp)]
            funext j; by_cases j1 : j = rTmp2; · subst j1; simp [Fin.ext_iff]
            by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
            simp [j1, j2]
        simp only [fibInnerStep, Function.update_of_ne (by decide : rF0 ≠ rTmp1), hU0]
        cases la with
        | nil =>
          dsimp only
          rw [hmid false _ (by simp [Fin.ext_iff, hUC])]
          funext j; by_cases j1 : j = rTmp2; · subst j1; simp [Fin.ext_iff]
          by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
          by_cases j3 : j = rF0; · subst j3; simp [Fin.ext_iff]
          by_cases j4 : j = rTmp1; · subst j4; simp [Fin.ext_iff]
          simp [j1, j2, j3, j4]
        | cons b0 la =>
          cases b0
          · dsimp only
            rw [hmid false _ (by simp [Fin.ext_iff, hUC])]
            funext j; by_cases j1 : j = rTmp2; · subst j1; simp [Fin.ext_iff]
            by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
            by_cases j3 : j = rF0; · subst j3; simp [Fin.ext_iff]
            by_cases j4 : j = rTmp1; · subst j4; simp [Fin.ext_iff]
            simp [j1, j2, j3, j4]
          · dsimp only
            rw [hmid true _ (by simp [Fin.ext_iff, hUC])]
            funext j; by_cases j1 : j = rTmp2; · subst j1; simp [Fin.ext_iff]
            by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
            by_cases j3 : j = rF0; · subst j3; simp [Fin.ext_iff]
            by_cases j4 : j = rTmp1; · subst j4; simp [Fin.ext_iff]
            simp [j1, j2, j3, j4]
      have htail_le : la.tail.length ≤ lb.length := by
        cases la <;> simp at hle ⊢ <;> omega
      have hrec := ih la.tail (fullAddCarry (la.headD false) b1 c) (fibInnerStep b1 U) htail_le
        (by rw [hstep]; simp [Fin.ext_iff]) (by rw [hstep]; simp [Fin.ext_iff])
      refine ⟨?_, hrec.2⟩
      rw [hrec.1, hstep]
      cases la with
      | nil =>
        funext j
        simp only [addBitsAux, List.headD_nil, List.tail_nil, List.reverse_cons,
          List.append_assoc, List.singleton_append]
        by_cases j1 : j = rTmp2; · subst j1; simp [Fin.ext_iff]
        by_cases j2 : j = rTmp1; · subst j2; simp [Fin.ext_iff]
        by_cases j3 : j = rCarry; · subst j3; simp [Fin.ext_iff]
        by_cases j4 : j = rF0; · subst j4; simp [Fin.ext_iff]
        simp [j1, j2, j3, j4]
      | cons b0 la =>
        funext j
        simp only [addBitsAux, List.headD_cons, List.tail_cons, List.reverse_cons,
          List.append_assoc, List.singleton_append]
        by_cases j1 : j = rTmp2; · subst j1; simp [Fin.ext_iff]
        by_cases j2 : j = rTmp1; · subst j2; simp [Fin.ext_iff]
        by_cases j3 : j = rCarry; · subst j3; simp [Fin.ext_iff]
        by_cases j4 : j = rF0; · subst j4; simp [Fin.ext_iff]
        simp [j1, j2, j3, j4]
  have hmain := hloop b.bits a.bits false (Function.update S rF1 []) hlen
    (by simp [Fin.ext_iff, hF0]) (by simp [Fin.ext_iff, hC])
  have hS3 : fibFinishCarry (clearExec rF0 ((S rF1).foldl (fun U b1 => fibInnerStep b1 U) (Function.update S rF1 []))) =
      Function.update (Function.update (Function.update (Function.update (Function.update S rF1 []) rF0 [])
        rCarry []) rTmp1 b.bits.reverse) rTmp2 (addBitsAux a.bits b.bits false).reverse := by
    rw [hF1, hmain.1]
    funext j
    by_cases j1 : j = rTmp2; · subst j1; simp [Fin.ext_iff, h2]
    by_cases j2 : j = rTmp1; · subst j2; simp [Fin.ext_iff, h1]
    by_cases j3 : j = rCarry; · subst j3; simp [Fin.ext_iff]
    by_cases j4 : j = rF0; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = rF1; · subst j5; simp [Fin.ext_iff]
    simp [j1, j2, j3, j4, j5]
  have hdrop : ((addBitsAux a.bits b.bits false).reverse.dropWhile (fun b => !b)).reverse = (a + b).bits := by
    rw [dropWhile_not_reverse, ofBits_addBitsAux, ofBits_bits, ofBits_bits]; simp
  refine ⟨?_, ?_⟩
  · simp only [fibStepExec]
    rw [hS3, stripFalseExec_eq]
    funext j
    simp only [revMoveExec, Function.update_self, Function.update_of_ne (by decide : rTmp1 ≠ rTmp2),
      Function.update_of_ne (by decide : rF0 ≠ rTmp2), Function.update_of_ne (by decide : rF0 ≠ rTmp1),
      Function.update_of_ne (by decide : rTmp2 ≠ rTmp1), Function.update_of_ne (by decide : rTmp2 ≠ rF0),
      Function.update_of_ne (by decide : rF1 ≠ rTmp1), Function.update_of_ne (by decide : rF1 ≠ rF0),
      Function.update_of_ne (by decide : rF1 ≠ rTmp2)]
    by_cases j1 : j = rF1; · subst j1; simp [Fin.ext_iff, hdrop]
    by_cases j2 : j = rF0; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = rTmp2; · subst j3; simp [Fin.ext_iff, h2]
    by_cases j4 : j = rTmp1; · subst j4; simp [Fin.ext_iff, h1]
    by_cases j5 : j = rCarry; · subst j5; simp [Fin.ext_iff, hC]
    simp [j1, j2, j3, j4, j5]
  · simp only [fibStepCost]
    have hS1f0 : (((S rF1).foldl (fun U b1 => fibInnerStep b1 U) (Function.update S rF1 [])) rF0).length = 0 := by
      rw [hF1]; exact hmain.2
    have hfc : forEachCost rF1 (fun b1 => fibInnerStep b1) (fun _ _ => 9) (S rF1) S ≤
        (S rF1).length * 11 + 1 :=
      forEachCost_le rF1 (fun b1 => fibInnerStep b1) (fun _ _ => 9) (fun _ => True) 9
        (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial) (S rF1) S trivial
    rw [hS3, hS1f0, hF1] at *
    simp only [stripFalseExec_eq, revMoveExec, Function.update_self,
      Function.update_of_ne (by decide : rTmp1 ≠ rTmp2),
      Function.update_of_ne (by decide : rTmp2 ≠ rTmp1),
      Function.update_of_ne (by decide : rTmp2 ≠ rF0)]
    have hlenAdd : (addBitsAux a.bits b.bits false).length ≤ b.bits.length + 1 :=
      addBitsAux_len_le b.bits a.bits false hlen
    have hlenDrop : ((addBitsAux a.bits b.bits false).reverse.dropWhile (fun x => !x)).length ≤
        (addBitsAux a.bits b.bits false).reverse.length :=
      (List.dropWhile_suffix _).length_le
    simp only [List.length_reverse] at hlenDrop ⊢
    omega

def computeFibExec (S : RK → List Bool) : RK → List Bool :=
  let S1 := Function.update S rF1 (true :: S rF1)
  let S2 := (S1 rL).foldl (fun U _ => fibStepExec U) (Function.update S1 rL [])
  clearExec rF1 S2

def computeFibCost (S : RK → List Bool) : ℕ :=
  let S1 := Function.update S rF1 (true :: S rF1)
  let S2 := (S1 rL).foldl (fun U _ => fibStepExec U) (Function.update S1 rL [])
  (3 * (S2 rF1).length + 1) +
    (forEachCost rL (fun _ => fibStepExec) (fun _ => fibStepCost) (S1 rL) S1 + 1)

theorem psb_computeFib : PureSB computeFibExec computeFibCost := by
  unfold computeFibExec computeFibCost
  exact psb_seq (psb_seq (psb_push rF1 true) (psb_forEachIgn rL psb_fibStep indep_fibStep))
    (psb_clear rF1)

theorem computeFib_spec (S : RK → List Bool)
    (hF0 : S rF0 = []) (hF1 : S rF1 = []) (h1 : S rTmp1 = []) (h2 : S rTmp2 = []) (hC : S rCarry = []) :
    computeFibExec S = Function.update (Function.update S rL []) rF0 (Nat.fib (S rL).length).bits ∧
    computeFibCost S ≤ 22 * ((S rL).length + 1) ^ 2 + 25 * ((S rL).length + 1) + 10 := by
  have hfold : ∀ (l : List Bool) (i : ℕ) (U : RK → List Bool),
      U rF0 = (Nat.fib i).bits → U rF1 = (Nat.fib (i + 1)).bits →
      U rTmp1 = [] → U rTmp2 = [] → U rCarry = [] →
      l.foldl (fun W _ => fibStepExec W) U =
        Function.update (Function.update U rF0 (Nat.fib (i + l.length)).bits)
          rF1 (Nat.fib (i + l.length + 1)).bits ∧
      forEachCost rL (fun _ => fibStepExec) (fun _ => fibStepCost) l U ≤
        l.length * (22 * (i + l.length) + 20) + 1 := by
    intro l
    induction l with
    | nil =>
      intro i U h0 h1' _ _ _
      refine ⟨?_, by simp [forEachCost]⟩
      funext j
      by_cases j1 : j = rF1; · subst j1; simp [Fin.ext_iff, h1']
      by_cases j2 : j = rF0; · subst j2; simp [Fin.ext_iff, h0]
      simp [j1, j2]
    | cons _ l ih =>
      intro i U h0 h1' ht1 ht2 hc
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have hmono : Nat.fib i ≤ Nat.fib (i + 1) := Nat.fib_mono (Nat.le_succ i)
      have hst1 := fibStep_spec U (Nat.fib i) (Nat.fib (i + 1)) hmono h0 h1' ht1 ht2 hc
      have hst2 := fibStep_spec (Function.update U rL l) (Nat.fib i) (Nat.fib (i + 1)) hmono
        (by simp [Fin.ext_iff, h0]) (by simp [Fin.ext_iff, h1']) (by simp [Fin.ext_iff, ht1]) (by simp [Fin.ext_iff, ht2]) (by simp [Fin.ext_iff, hc])
      have hfib : Nat.fib i + Nat.fib (i + 1) = Nat.fib (i + 2) := (Nat.fib_add_two).symm
      rw [hfib] at hst1 hst2
      have hrec1 := ih (i + 1) (fibStepExec U) (by rw [hst1.1]; simp [Fin.ext_iff]) (by rw [hst1.1]; simp)
        (by rw [hst1.1]; simp [Fin.ext_iff, ht1]) (by rw [hst1.1]; simp [Fin.ext_iff, ht2]) (by rw [hst1.1]; simp [Fin.ext_iff, hc])
      have hrec2 := ih (i + 1) (fibStepExec (Function.update U rL l))
        (by rw [hst2.1]; simp [Fin.ext_iff]) (by rw [hst2.1]; simp)
        (by rw [hst2.1]; simp [Fin.ext_iff, ht1]) (by rw [hst2.1]; simp [Fin.ext_iff, ht2]) (by rw [hst2.1]; simp [Fin.ext_iff, hc])
      refine ⟨?_, ?_⟩
      · rw [hrec1.1, hst1.1]
        have he1 : i + 1 + l.length = i + (l.length + 1) := by omega
        rw [he1]
        funext j
        by_cases j1 : j = rF1; · subst j1; simp [Fin.ext_iff]
        by_cases j2 : j = rF0; · subst j2; simp [Fin.ext_iff]
        simp [j1, j2]
      · have hlen : (Nat.fib (i + 1)).bits.length ≤ i + 1 := fib_bits_length_le (i + 1)
        have hcost1 : fibStepCost (Function.update U rL l) ≤ 22 * (i + 1) + 18 := by
          have := hst2.2; omega
        have hcost2 := hrec2.2
        have he1 : i + 1 + l.length = i + (l.length + 1) := by omega
        rw [he1] at hcost2
        have hmul : (l.length + 1) * (22 * (i + (l.length + 1)) + 20) =
            l.length * (22 * (i + (l.length + 1)) + 20) + (22 * (i + (l.length + 1)) + 20) := by ring
        omega
  have hS1L : (Function.update S rF1 (true :: S rF1)) rL = S rL := by simp [Fin.ext_iff]
  have hf0 : (Nat.fib 0).bits = [] := rfl
  have hf1 : (Nat.fib 1).bits = [true] := rfl
  have hres1 := hfold (S rL) 0 (Function.update (Function.update S rF1 (true :: S rF1)) rL [])
    (by simp [Fin.ext_iff, hF0, hf0]) (by simp [Fin.ext_iff, hF1, hf1]) (by simp [Fin.ext_iff, h1]) (by simp [Fin.ext_iff, h2]) (by simp [Fin.ext_iff, hC])
  have hres2 := hfold (S rL) 0 (Function.update S rF1 (true :: S rF1))
    (by simp [Fin.ext_iff, hF0, hf0]) (by simp [Fin.ext_iff, hF1, hf1]) (by simp [Fin.ext_iff, h1]) (by simp [Fin.ext_iff, h2]) (by simp [Fin.ext_iff, hC])
  refine ⟨?_, ?_⟩
  · simp only [computeFibExec, hS1L, hres1.1, clearExec, Nat.zero_add]
    funext j
    by_cases j1 : j = rF1; · subst j1; simp [Fin.ext_iff, hF1]
    by_cases j2 : j = rF0; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = rL; · subst j3; simp [Fin.ext_iff]
    simp [j1, j2, j3]
  · simp only [computeFibCost, hS1L, hres1.1, Nat.zero_add, Function.update_self]
    have hfl := fib_bits_length_le ((S rL).length + 1)
    have hfc := hres2.2
    simp only [Nat.zero_add] at hfc
    have hsq : ((S rL).length + 1) ^ 2 = ((S rL).length + 1) * ((S rL).length + 1) := sq _
    nlinarith

def shiftBitExec (bit : Bool) (S : RK → List Bool) : RK → List Bool :=
  if bit then Function.update S rRem (true :: S rRem)
  else match S rRem with
    | [] => Function.update S rRem []
    | false :: l => Function.update S rRem (false :: false :: l)
    | true :: l => Function.update S rRem (false :: true :: l)

theorem psb_shiftBit (bit : Bool) : PureSB (shiftBitExec bit) (fun _ => 5) := by
  cases bit
  · have hF : PureSB (fun U : RK → List Bool => Function.update U rRem (false :: false :: U rRem)) (fun _ => 2) := by
      refine psb_congr (psb_seq (psb_push rRem false) (psb_push rRem false)) ?_
      intro U; funext j; by_cases hj : j = rRem; · subst hj; simp
      simp [hj]
    have hT : PureSB (fun U : RK → List Bool => Function.update U rRem (false :: true :: U rRem)) (fun _ => 2) := by
      refine psb_congr (psb_seq (psb_push rRem true) (psb_push rRem false)) ?_
      intro U; funext j; by_cases hj : j = rRem; · subst hj; simp
      simp [hj]
    have hbr := psb_branchPop rRem psb_noop hF hT
    refine psb_mono (psb_congr hbr ?_) ?_
    · intro S; cases h : S rRem with
      | nil => simp [shiftBitExec, h]
      | cons b l =>
        cases b
        · funext j; simp only [shiftBitExec, h, Bool.false_eq_true, ↓reduceIte]
          by_cases hj : j = rRem; · subst hj; simp
          simp [hj]
        · funext j; simp only [shiftBitExec, h, Bool.false_eq_true, ↓reduceIte]
          by_cases hj : j = rRem; · subst hj; simp
          simp [hj]
    · intro S; cases S rRem with | nil => simp | cons b _ => cases b <;> simp
  · refine psb_mono (psb_congr (psb_push rRem true) (fun _ => rfl)) (fun _ => by decide)

theorem indep_shiftBit (bit : Bool) : Indep rRrev (shiftBitExec bit) := by
  intro S l
  cases bit
  · simp only [shiftBitExec, Bool.false_eq_true, ↓reduceIte, Function.update_of_ne (by decide : rRem ≠ rRrev)]
    cases S rRem with
    | nil =>
      funext j
      by_cases h1 : j = rRrev; · subst h1; simp [Fin.ext_iff]
      by_cases h2 : j = rRem; · subst h2; simp [Fin.ext_iff]
      simp [h1, h2]
    | cons b lr =>
      cases b
      · funext j
        by_cases h1 : j = rRrev; · subst h1; simp [Fin.ext_iff]
        by_cases h2 : j = rRem; · subst h2; simp [Fin.ext_iff]
        simp [h1, h2]
      · funext j
        by_cases h1 : j = rRrev; · subst h1; simp [Fin.ext_iff]
        by_cases h2 : j = rRem; · subst h2; simp [Fin.ext_iff]
        simp [h1, h2]
  · simp only [shiftBitExec, ↓reduceIte]
    funext j
    by_cases h1 : j = rRrev; · subst h1; simp [Fin.ext_iff]
    by_cases h2 : j = rRem; · subst h2; simp [Fin.ext_iff]
    simp [h1, h2]

theorem shiftBitExec_bits (bit : Bool) (m : ℕ) (S : RK → List Bool) (hR : S rRem = m.bits) :
    shiftBitExec bit S = Function.update S rRem (2 * m + bit.toNat).bits := by
  cases bit
  · simp only [shiftBitExec, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero]
    by_cases hm : m = 0
    · subst hm; simp [Fin.ext_iff, hR]
    · have hne : m.bits ≠ [] := by
        intro h; have := congrArg ofBits h; rw [ofBits_bits] at this; exact hm this
      cases hb : m.bits with
      | nil => exact absurd hb hne
      | cons b l =>
        have hbits : (2 * m).bits = false :: m.bits := by
          have : 2 * m = Nat.bit false m := by rw [Nat.bit_val]; simp
          rw [this, Nat.bits_append_bit m false (fun h => absurd h hm)]
        rw [hR, hb, hbits, hb]; cases b <;> rfl
  · simp only [shiftBitExec, ↓reduceIte, Bool.toNat_true, hR]
    have hbits : (2 * m + 1).bits = true :: m.bits := by
      have : 2 * m + 1 = Nat.bit true m := by rw [Nat.bit_val]; simp
      rw [this, Nat.bits_append_bit m true (fun _ => rfl)]
    rw [hbits]

def subBitCore (rb bb bor : Bool) (S : RK → List Bool) : RK → List Bool :=
  let S1 := Function.update S rDiff (fullSubDiff rb bb bor :: S rDiff)
  if fullSubBor rb bb bor then Function.update S1 rCarry (true :: S1 rCarry) else S1

theorem psb_subBitCore (rb bb bor : Bool) : PureSB (subBitCore rb bb bor) (fun _ => 2) := by
  have h1 := psb_push rDiff (fullSubDiff rb bb bor)
  cases hc : fullSubBor rb bb bor
  · exact psb_congr (psb_seq h1 psb_noop) (fun S => by simp [subBitCore, hc])
  · exact psb_congr (psb_seq h1 (psb_push rCarry true)) (fun S => by simp [subBitCore, hc])

def subStepCarry (rb bb : Bool) (S : RK → List Bool) : RK → List Bool :=
  let S1 := Function.update S rTmp1 (rb :: S rTmp1)
  match S1 rCarry with
  | [] => subBitCore rb bb false (Function.update S1 rCarry [])
  | false :: l => subBitCore rb bb false (Function.update S1 rCarry l)
  | true :: l => subBitCore rb bb true (Function.update S1 rCarry l)

theorem psb_subStepCarry (rb bb : Bool) : PureSB (subStepCarry rb bb) (fun _ => 6) := by
  unfold subStepCarry
  have hbr := psb_branchPop rCarry (psb_subBitCore rb bb false) (psb_subBitCore rb bb false)
    (psb_subBitCore rb bb true)
  have hbr' : PureSB _ (fun _ => 5) := psb_mono hbr (fun S => by
    cases S rCarry with | nil => simp | cons b _ => cases b <;> simp)
  exact psb_seq (psb_push rTmp1 rb) hbr'

def subPass1Step (bb : Bool) (S : RK → List Bool) : RK → List Bool :=
  let S1 := Function.update S rTmp2 (bb :: S rTmp2)
  match S1 rRem with
  | [] => Function.update (Function.update S1 rRem []) rUnder (true :: (Function.update S1 rRem []) rUnder)
  | false :: l => subStepCarry false bb (Function.update S1 rRem l)
  | true :: l => subStepCarry true bb (Function.update S1 rRem l)

theorem psb_subPass1Step (bb : Bool) : PureSB (subPass1Step bb) (fun _ => 10) := by
  unfold subPass1Step
  have hbr := psb_branchPop rRem (psb_push rUnder true) (psb_subStepCarry false bb) (psb_subStepCarry true bb)
  have hbr' : PureSB _ (fun _ => 9) := psb_mono hbr (fun S => by
    cases S rRem with | nil => simp | cons b _ => cases b <;> simp)
  exact psb_seq (psb_push rTmp2 bb) hbr'

theorem indep_subBitCore {k : RK} (h1 : rDiff ≠ k) (h2 : rCarry ≠ k) (rb bb bor : Bool) :
    Indep k (subBitCore rb bb bor) := by
  intro S l; funext j; simp only [subBitCore]
  cases fullSubBor rb bb bor
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases j1 : j = k; · subst j1; simp [h1.symm]
    by_cases j2 : j = rDiff; · subst j2; simp [h1]
    simp [j1, j2]
  · simp only [↓reduceIte]
    by_cases j1 : j = k; · subst j1; simp [h1.symm, h2.symm]
    by_cases j2 : j = rCarry; · subst j2; simp [h2, Fin.ext_iff]
    by_cases j3 : j = rDiff; · subst j3; simp [h1, Fin.ext_iff]
    simp [j1, j2, j3]

theorem indep_subStepCarry {k : RK} (h1 : rTmp1 ≠ k) (h2 : rCarry ≠ k) (h3 : rDiff ≠ k) (rb bb : Bool) :
    Indep k (subStepCarry rb bb) := by
  intro S l
  simp only [subStepCarry]
  have hu : Function.update (Function.update S k l) rTmp1 (rb :: Function.update S k l rTmp1) =
      Function.update (Function.update S rTmp1 (rb :: S rTmp1)) k l := by
    funext j
    by_cases j1 : j = k; · subst j1; simp [h1.symm]
    by_cases j2 : j = rTmp1; · subst j2; simp [h1]
    simp [j1, j2]
  rw [hu, Function.update_of_ne h2]
  cases (Function.update S rTmp1 (rb :: S rTmp1)) rCarry with
  | nil => dsimp only; rw [Function.update_comm h2.symm, indep_subBitCore h3 h2]
  | cons b lc => cases b <;> (dsimp only; rw [Function.update_comm h2.symm, indep_subBitCore h3 h2])

theorem indep_subPass1Step {k : RK} (h1 : rTmp2 ≠ k) (h2 : rRem ≠ k) (h3 : rUnder ≠ k)
    (h4 : rTmp1 ≠ k) (h5 : rCarry ≠ k) (h6 : rDiff ≠ k) (bb : Bool) :
    Indep k (subPass1Step bb) := by
  intro S l
  simp only [subPass1Step]
  have hu : Function.update (Function.update S k l) rTmp2 (bb :: Function.update S k l rTmp2) =
      Function.update (Function.update S rTmp2 (bb :: S rTmp2)) k l := by
    funext j
    by_cases j1 : j = k; · subst j1; simp [h1.symm]
    by_cases j2 : j = rTmp2; · subst j2; simp [h1]
    simp [j1, j2]
  rw [hu, Function.update_of_ne h2]
  cases (Function.update S rTmp2 (bb :: S rTmp2)) rRem with
  | nil =>
    dsimp only; funext j
    by_cases j1 : j = k; · subst j1; simp [h2.symm, h3.symm]
    by_cases j2 : j = rUnder; · subst j2; simp [h3, Fin.ext_iff]
    by_cases j3 : j = rRem; · subst j3; simp [h2, Fin.ext_iff]
    simp [j1, j2, j3]
  | cons b lr =>
    cases b <;> (dsimp only; rw [Function.update_comm h2.symm, indep_subStepCarry h4 h5 h6])

def subCommitExec (S : RK → List Bool) : RK → List Bool :=
  revMoveExec rDiff rRem (stripFalseExec rDiff (clearExec rTmp1 S))

def subCommitCost (S : RK → List Bool) : ℕ :=
  let S1 := clearExec rTmp1 S
  let S2 := stripFalseExec rDiff S1
  (3 * (S2 rDiff).length + 1) + ((2 * (S1 rDiff).length + 3) + (3 * (S rTmp1).length + 1))

theorem psb_subCommit : PureSB subCommitExec subCommitCost := by
  unfold subCommitExec subCommitCost
  exact psb_seq (psb_seq (psb_clear rTmp1) (psb_stripFalse rDiff))
    (psb_revMove (a := rDiff) (b := rRem) (by decide))

def subAbortExec (S : RK → List Bool) : RK → List Bool :=
  revMoveExec rTmp1 rRem (clearExec rDiff (clearExec rCarry (clearExec rUnder S)))

def subAbortCost (S : RK → List Bool) : ℕ :=
  let S1 := clearExec rUnder S
  let S2 := clearExec rCarry S1
  let S3 := clearExec rDiff S2
  (3 * (S3 rTmp1).length + 1) + ((3 * (S2 rDiff).length + 1) +
    ((3 * (S1 rCarry).length + 1) + (3 * (S rUnder).length + 1)))

theorem psb_subAbort : PureSB subAbortExec subAbortCost := by
  unfold subAbortExec subAbortCost
  exact psb_seq (psb_seq (psb_seq (psb_clear rUnder) (psb_clear rCarry)) (psb_clear rDiff))
    (psb_revMove (a := rTmp1) (b := rRem) (by decide))

def subDecideExec (S : RK → List Bool) : RK → List Bool :=
  match S rUnder with
  | [] =>
    let S1 := Function.update S rUnder []
    match S1 rCarry with
    | [] => subCommitExec (Function.update S1 rCarry [])
    | false :: l => subAbortExec (Function.update S1 rCarry l)
    | true :: l => subAbortExec (Function.update S1 rCarry l)
  | false :: l => subAbortExec (Function.update S rUnder l)
  | true :: l => subAbortExec (Function.update S rUnder l)

def subDecideCost (S : RK → List Bool) : ℕ :=
  match S rUnder with
  | [] =>
    let S1 := Function.update S rUnder []
    (match S1 rCarry with
     | [] => subCommitCost (Function.update S1 rCarry []) + 2
     | false :: l => subAbortCost (Function.update S1 rCarry l) + 3
     | true :: l => subAbortCost (Function.update S1 rCarry l) + 3) + 2
  | false :: l => subAbortCost (Function.update S rUnder l) + 3
  | true :: l => subAbortCost (Function.update S rUnder l) + 3

theorem psb_subDecide : PureSB subDecideExec subDecideCost := by
  unfold subDecideExec subDecideCost
  exact psb_branchPop rUnder (psb_branchPop rCarry psb_subCommit psb_subAbort psb_subAbort)
    psb_subAbort psb_subAbort

def geSubExec (S : RK → List Bool) : RK → List Bool :=
  let S1 := (S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])
  let S2 := (S1 rRem).foldl (fun U rb => subStepCarry rb false U) (Function.update S1 rRem [])
  let S3 := revMoveExec rTmp2 rF0 S2
  subDecideExec S3

def geSubCost (S : RK → List Bool) : ℕ :=
  let S1 := (S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])
  let S2 := (S1 rRem).foldl (fun U rb => subStepCarry rb false U) (Function.update S1 rRem [])
  let S3 := revMoveExec rTmp2 rF0 S2
  subDecideCost S3 +
    ((3 * (S2 rTmp2).length + 1) +
      (forEachCost rRem (fun rb => subStepCarry rb false) (fun _ _ => 6) (S1 rRem) S1 +
       forEachCost rF0 (fun bb => subPass1Step bb) (fun _ _ => 10) (S rF0) S))

theorem psb_geSub : PureSB geSubExec geSubCost := by
  unfold geSubExec geSubCost
  exact psb_seq
    (psb_seq
      (psb_seq
        (psb_forEach rF0 (step := fun bb => subPass1Step bb) (B := fun _ _ => 10)
          (psb_subPass1Step false) (psb_subPass1Step true)
          (fun bb => indep_subPass1Step (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) bb))
        (psb_forEach rRem (step := fun rb => subStepCarry rb false) (B := fun _ _ => 6)
          (psb_subStepCarry false false) (psb_subStepCarry true false)
          (fun rb => indep_subStepCarry (by decide) (by decide) (by decide) rb false)))
      (psb_revMove (a := rTmp2) (b := rF0) (by decide)))
    psb_subDecide

theorem indep_geSub : Indep rRrev geSubExec := by
  unfold geSubExec
  have h1 : Indep rRrev (fun S => (S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) := by
    intro S l; dsimp only
    rw [Function.update_of_ne (by decide : rF0 ≠ rRrev), Function.update_comm (by decide : rRrev ≠ rF0)]
    generalize S rF0 = lb; generalize Function.update S rF0 [] = U
    induction lb generalizing U with
    | nil => rfl
    | cons bb lb ih =>
      simp only [List.foldl_cons]
      rw [indep_subPass1Step (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) bb, ih]
  have h2 : Indep rRrev (fun S => (S rRem).foldl (fun U rb => subStepCarry rb false U) (Function.update S rRem [])) := by
    intro S l; dsimp only
    rw [Function.update_of_ne (by decide : rRem ≠ rRrev), Function.update_comm (by decide : rRrev ≠ rRem)]
    generalize S rRem = lr; generalize Function.update S rRem [] = U
    induction lr generalizing U with
    | nil => rfl
    | cons rb lr ih =>
      simp only [List.foldl_cons]
      rw [indep_subStepCarry (by decide) (by decide) (by decide) rb false, ih]
  have hdec : Indep rRrev subDecideExec := by
    have hcom : Indep rRrev subCommitExec := by
      unfold subCommitExec
      exact indep_seq (indep_seq (indep_clear (a := rTmp1) (by decide)) (indep_stripFalse (d := rDiff) (by decide)))
        (indep_revMove (a := rDiff) (b := rRem) (by decide) (by decide))
    have hab : Indep rRrev subAbortExec := by
      unfold subAbortExec
      exact indep_seq (indep_seq (indep_seq (indep_clear (a := rUnder) (by decide)) (indep_clear (a := rCarry) (by decide)))
        (indep_clear (a := rDiff) (by decide))) (indep_revMove (a := rTmp1) (b := rRem) (by decide) (by decide))
    intro S l
    simp only [subDecideExec, Function.update_of_ne (by decide : rUnder ≠ rRrev)]
    cases S rUnder with
    | nil =>
      dsimp only
      rw [Function.update_comm (by decide : rRrev ≠ rUnder), Function.update_of_ne (by decide : rCarry ≠ rRrev)]
      cases Function.update S rUnder [] rCarry with
      | nil => dsimp only; rw [Function.update_comm (by decide : rRrev ≠ rCarry), hcom]
      | cons b lc => cases b <;> (dsimp only; rw [Function.update_comm (by decide : rRrev ≠ rCarry), hab])
    | cons b lu => cases b <;> (dsimp only; rw [Function.update_comm (by decide : rRrev ≠ rUnder), hab])
  exact indep_seq (indep_seq (indep_seq h1 h2) (indep_revMove (a := rTmp2) (b := rF0) (by decide) (by decide))) hdec

theorem subBitCore_eq (rb bb bor : Bool) (W : RK → List Bool) (hC : W rCarry = []) :
    subBitCore rb bb bor W =
      Function.update (Function.update W rCarry (if fullSubBor rb bb bor then [true] else []))
        rDiff (fullSubDiff rb bb bor :: W rDiff) := by
  funext j; simp only [subBitCore]
  by_cases j1 : j = rDiff; · subst j1; cases fullSubBor rb bb bor <;> simp [Fin.ext_iff]
  by_cases j2 : j = rCarry; · subst j2; cases fullSubBor rb bb bor <;> simp [hC, Fin.ext_iff]
  cases fullSubBor rb bb bor <;> simp [j1, j2]

theorem subStepCarry_eq (rb bb bor : Bool) (U : RK → List Bool)
    (hC : U rCarry = (if bor then [true] else [])) :
    subStepCarry rb bb U =
      Function.update (Function.update (Function.update U rTmp1 (rb :: U rTmp1))
        rCarry (if fullSubBor rb bb bor then [true] else []))
        rDiff (fullSubDiff rb bb bor :: U rDiff) := by
  simp only [subStepCarry, Function.update_of_ne (by decide : rCarry ≠ rTmp1), hC]
  cases bor
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [subBitCore_eq rb bb false _ (by simp)]
    funext j
    by_cases j1 : j = rDiff; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff]
    simp [j1, j2, j3]
  · simp only [↓reduceIte]
    rw [subBitCore_eq rb bb true _ (by simp)]
    funext j
    by_cases j1 : j = rDiff; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff]
    simp [j1, j2, j3]

theorem subPass1Step_cons_eq (bb a : Bool) (la : List Bool) (bor : Bool) (U : RK → List Bool)
    (hR : U rRem = a :: la) (hC : U rCarry = (if bor then [true] else [])) :
    subPass1Step bb U =
      Function.update (Function.update (Function.update (Function.update (Function.update U
        rRem la) rTmp2 (bb :: U rTmp2)) rTmp1 (a :: U rTmp1))
        rCarry (if fullSubBor a bb bor then [true] else []))
        rDiff (fullSubDiff a bb bor :: U rDiff) := by
  simp only [subPass1Step, Function.update_of_ne (by decide : rRem ≠ rTmp2), hR]
  cases a
  · dsimp only
    rw [subStepCarry_eq false bb bor _ (by simp [Fin.ext_iff, hC])]
    funext j
    by_cases j1 : j = rDiff; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff]
    by_cases j4 : j = rTmp2; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = rRem; · subst j5; simp [Fin.ext_iff]
    simp [j1, j2, j3, j4, j5]
  · dsimp only
    rw [subStepCarry_eq true bb bor _ (by simp [Fin.ext_iff, hC])]
    funext j
    by_cases j1 : j = rDiff; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff]
    by_cases j4 : j = rTmp2; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = rRem; · subst j5; simp [Fin.ext_iff]
    simp [j1, j2, j3, j4, j5]

theorem geSub_spec (S : RK → List Bool) (rem b : ℕ) (hb : 0 < b) (hlt : rem < 2 * b)
    (hRem : S rRem = rem.bits) (hF0 : S rF0 = b.bits)
    (hD : S rDiff = []) (h1 : S rTmp1 = []) (h2 : S rTmp2 = []) (hC : S rCarry = []) (hU : S rUnder = []) :
    geSubExec S = Function.update S rRem (rem % b).bits ∧
    geSubCost S ≤ 40 * b.bits.length + 45 := by
  have hrem_len : rem.bits.length ≤ b.bits.length + 1 := by
    have hlt2 : rem < 2 ^ (b.bits.length + 1) := by
      have h1 := ofBits_lt_two_pow b.bits
      rw [ofBits_bits] at h1
      rw [pow_succ']; omega
    exact bits_length_le_of_lt_pow hlt2
  have hpass2 : ∀ (la : List Bool) (bor : Bool) (U : RK → List Bool),
      U rCarry = (if bor then [true] else []) →
      la.foldl (fun W rb => subStepCarry rb false W) U =
        Function.update (Function.update (Function.update U rTmp1 (la.reverse ++ U rTmp1))
          rCarry (if (subBitsAux la [] bor).2 then [true] else []))
          rDiff ((subBitsAux la [] bor).1.reverse ++ U rDiff) := by
    intro la
    induction la with
    | nil =>
      intro bor U hUC
      funext j; simp only [List.foldl_nil, subBitsAux, List.reverse_nil, List.nil_append]
      by_cases j1 : j = rDiff; · subst j1; simp [Fin.ext_iff]
      by_cases j2 : j = rCarry; · subst j2; cases bor <;> simp [Fin.ext_iff, hUC]
      by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff]
      simp [j1, j2, j3]
    | cons a la ih =>
      intro bor U hUC
      simp only [List.foldl_cons]
      have hst : subStepCarry a false U =
          Function.update (Function.update (Function.update U rTmp1 (a :: U rTmp1))
            rCarry (if fullSubBor a false bor then [true] else []))
            rDiff (fullSubDiff a false bor :: U rDiff) := subStepCarry_eq a false bor U hUC
      rw [hst, ih (fullSubBor a false bor) _ (by simp [Fin.ext_iff])]
      funext j; simp only [subBitsAux, List.reverse_cons, List.append_assoc, List.singleton_append]
      by_cases j1 : j = rDiff; · subst j1; simp [Fin.ext_iff]
      by_cases j2 : j = rCarry
      · subst j2
        simp only [Function.update_of_ne (by decide : rCarry ≠ rDiff), Function.update_self]; rfl
      by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff]
      simp [j1, j2, j3]
  by_cases hle : b.bits.length ≤ rem.bits.length
  ·
    have hpass1 : ∀ (lb la : List Bool) (bor : Bool) (U : RK → List Bool),
        lb.length ≤ la.length → U rRem = la → U rCarry = (if bor then [true] else []) →
        let la1 := la.take lb.length
        let la2 := la.drop lb.length
        let res := subBitsAux la1 lb bor
        lb.foldl (fun W bb => subPass1Step bb W) U =
          Function.update (Function.update (Function.update (Function.update (Function.update U
            rRem la2) rTmp2 (lb.reverse ++ U rTmp2)) rTmp1 (la1.reverse ++ U rTmp1))
            rCarry (if res.2 then [true] else []))
            rDiff (res.1.reverse ++ U rDiff) := by
      intro lb
      induction lb with
      | nil =>
        intro la bor U _ hUR hUC
        funext j; simp only [List.foldl_nil, List.length_nil, List.take_zero, List.drop_zero,
          subBitsAux, List.reverse_nil, List.nil_append]
        by_cases j1 : j = rDiff; · subst j1; simp [Fin.ext_iff]
        by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff, hUC]
        by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff]
        by_cases j4 : j = rTmp2; · subst j4; simp [Fin.ext_iff]
        by_cases j5 : j = rRem; · subst j5; simp [Fin.ext_iff, hUR]
        simp [j1, j2, j3, j4, j5]
      | cons bb lb ih =>
        intro la bor U hlen hUR hUC
        cases la with
        | nil => simp at hlen
        | cons a la =>
          simp only [List.length_cons] at hlen
          simp only [List.foldl_cons]
          have hst : subPass1Step bb U =
              Function.update (Function.update (Function.update (Function.update (Function.update U
                rRem la) rTmp2 (bb :: U rTmp2)) rTmp1 (a :: U rTmp1))
                rCarry (if fullSubBor a bb bor then [true] else []))
                rDiff (fullSubDiff a bb bor :: U rDiff) := subPass1Step_cons_eq bb a la bor U hUR hUC
          rw [hst, ih la (fullSubBor a bb bor) _ (by omega) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
          funext j
          simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons, subBitsAux,
            List.reverse_cons, List.append_assoc, List.singleton_append]
          by_cases j1 : j = rDiff; · subst j1; simp [Fin.ext_iff]
          by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
          by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff]
          by_cases j4 : j = rTmp2; · subst j4; simp [Fin.ext_iff]
          by_cases j5 : j = rRem; · subst j5; simp [Fin.ext_iff]
          simp [j1, j2, j3, j4, j5]
    have hsplit : ∀ (lb la : List Bool) (bor : Bool), lb.length ≤ la.length →
        let r1 := subBitsAux (la.take lb.length) lb bor
        let r2 := subBitsAux (la.drop lb.length) [] r1.2
        subBitsAux la lb bor = (r1.1 ++ r2.1, r2.2) := by
      intro lb
      induction lb with
      | nil => intro la bor _; simp [subBitsAux]
      | cons bb lb ih =>
        intro la bor hlen
        cases la with
        | nil => simp at hlen
        | cons a la =>
          simp only [List.length_cons] at hlen
          have hrec := ih la (fullSubBor a bb bor) (by omega)
          simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons, subBitsAux]
          rw [hrec]; simp
    have hS1 : (S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 []) =
        let la1 := rem.bits.take b.bits.length
        let la2 := rem.bits.drop b.bits.length
        let res := subBitsAux la1 b.bits false
        Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update S rF0 []) rRem la2) rTmp2 b.bits.reverse) rTmp1 la1.reverse)
          rCarry (if res.2 then [true] else [])) rDiff res.1.reverse := by
      rw [hF0, hpass1 b.bits rem.bits false (Function.update S rF0 []) hle (by simp [Fin.ext_iff, hRem]) (by simp [Fin.ext_iff, hC])]
      funext j
      by_cases j1 : j = rDiff; · subst j1; simp [Fin.ext_iff, hD]
      by_cases j2 : j = rCarry; · subst j2; simp [Fin.ext_iff]
      by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff, h1]
      by_cases j4 : j = rTmp2; · subst j4; simp [Fin.ext_iff, h2]
      by_cases j5 : j = rRem; · subst j5; simp [Fin.ext_iff]
      by_cases j6 : j = rF0; · subst j6; simp [Fin.ext_iff]
      simp [j1, j2, j3, j4, j5, j6]
    have hS3 : revMoveExec rTmp2 rF0
        (((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem |>.foldl
          (fun U rb => subStepCarry rb false U)
          (Function.update ((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem [])) =
        let res := subBitsAux rem.bits b.bits false
        Function.update (Function.update (Function.update (Function.update S
          rRem []) rTmp1 rem.bits.reverse) rCarry (if res.2 then [true] else [])) rDiff res.1.reverse := by
      rw [hS1]
      simp only [Function.update_of_ne (by decide : rRem ≠ rDiff),
        Function.update_of_ne (by decide : rRem ≠ rCarry),
        Function.update_of_ne (by decide : rRem ≠ rTmp1),
        Function.update_of_ne (by decide : rRem ≠ rTmp2), Function.update_self]
      rw [hpass2 (rem.bits.drop b.bits.length) (subBitsAux (rem.bits.take b.bits.length) b.bits false).2 _ (by simp [Fin.ext_iff])]
      have hsp := hsplit b.bits rem.bits false hle
      have hrev_app : (rem.bits.drop b.bits.length).reverse ++ (rem.bits.take b.bits.length).reverse =
          rem.bits.reverse := by
        rw [← List.reverse_append, List.take_append_drop]
      have hres1 : (subBitsAux (rem.bits.drop b.bits.length) []
          (subBitsAux (rem.bits.take b.bits.length) b.bits false).2).1.reverse ++
          (subBitsAux (rem.bits.take b.bits.length) b.bits false).1.reverse =
          (subBitsAux rem.bits b.bits false).1.reverse := by
        rw [hsp, List.reverse_append]
      have hres2 : (subBitsAux (rem.bits.drop b.bits.length) []
          (subBitsAux (rem.bits.take b.bits.length) b.bits false).2).2 =
          (subBitsAux rem.bits b.bits false).2 := by
        rw [hsp]
      funext j
      simp only [revMoveExec]
      by_cases j1 : j = rF0; · subst j1; simp [Fin.ext_iff, hF0]
      by_cases j2 : j = rTmp2; · subst j2; simp [Fin.ext_iff, h2]
      by_cases j3 : j = rDiff; · subst j3; simp [Fin.ext_iff, hres1]
      by_cases j4 : j = rCarry; · subst j4; simp [Fin.ext_iff, hres2]
      by_cases j5 : j = rTmp1; · subst j5; simp [Fin.ext_iff, hrev_app]
      by_cases j6 : j = rRem; · subst j6; simp [Fin.ext_iff]
      simp [j1, j2, j3, j4, j5, j6]
    have hsub := subBitsAux_spec rem.bits b.bits false hle
    rw [ofBits_bits, ofBits_bits] at hsub
    have hcost1 : forEachCost rF0 (fun bb => subPass1Step bb) (fun _ _ => 10) (S rF0) S ≤
        12 * b.bits.length + 1 := by
      have hfl : (S rF0).length = b.bits.length := by rw [hF0]
      have := forEachCost_le rF0 (fun bb => subPass1Step bb) (fun _ _ => 10) (fun _ => True) 10
        (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial) (S rF0) S trivial
      rw [hfl] at this; omega
    have hcost2 : forEachCost rRem (fun rb => subStepCarry rb false) (fun _ _ => 6)
        (((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem)
        ((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) ≤
        8 * (rem.bits.drop b.bits.length).length + 1 := by
      have hlen2 : (((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem).length =
          (rem.bits.drop b.bits.length).length := by
        rw [hS1]; simp [Fin.ext_iff]
      have := forEachCost_le rRem (fun rb => subStepCarry rb false) (fun _ _ => 6) (fun _ => True) 6
        (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial)
        (((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem)
        ((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) trivial
      rw [hlen2] at this
      omega
    have hS2t2 : (((((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem).foldl
        (fun U rb => subStepCarry rb false U)
        (Function.update ((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem [])) rTmp2).length =
        b.bits.length := by
      rw [hS1]
      simp only [Function.update_of_ne (by decide : rRem ≠ rDiff),
        Function.update_of_ne (by decide : rRem ≠ rCarry),
        Function.update_of_ne (by decide : rRem ≠ rTmp1),
        Function.update_of_ne (by decide : rRem ≠ rTmp2), Function.update_self]
      rw [hpass2 (rem.bits.drop b.bits.length) (subBitsAux (rem.bits.take b.bits.length) b.bits false).2 _ (by simp [Fin.ext_iff])]
      simp [Fin.ext_iff]
    cases hbor : (subBitsAux rem.bits b.bits false).2
    ·
      have hge : b ≤ rem ∧ ofBits (subBitsAux rem.bits b.bits false).1 = rem - b := by
        rw [hbor] at hsub; simp at hsub; omega
      have hmod : rem % b = rem - b := by
        rw [Nat.mod_eq_sub_mod hge.1, Nat.mod_eq_of_lt (by omega)]
      refine ⟨?_, ?_⟩
      · simp only [geSubExec]
        rw [hS3]; dsimp only; rw [hbor]
        simp only [Bool.false_eq_true, ↓reduceIte, subDecideExec,
          Function.update_of_ne (by decide : rUnder ≠ rDiff),
          Function.update_of_ne (by decide : rUnder ≠ rCarry),
          Function.update_of_ne (by decide : rUnder ≠ rTmp1),
          Function.update_of_ne (by decide : rUnder ≠ rRem), hU,
          Function.update_of_ne (by decide : rCarry ≠ rUnder),
          Function.update_of_ne (by decide : rCarry ≠ rDiff), Function.update_self,
          subCommitExec, clearExec, stripFalseExec_eq, revMoveExec]
        have hdr : ((subBitsAux rem.bits b.bits false).1.reverse.dropWhile (fun x => !x)).reverse =
            (rem % b).bits := by
          rw [dropWhile_not_reverse, hge.2, hmod]
        funext j
        by_cases j1 : j = rRem; · subst j1; simp [Fin.ext_iff, hdr]
        by_cases j2 : j = rDiff; · subst j2; simp [Fin.ext_iff, hD]
        by_cases j3 : j = rTmp1; · subst j3; simp [Fin.ext_iff, h1]
        by_cases j4 : j = rCarry; · subst j4; simp [Fin.ext_iff, hC]
        by_cases j5 : j = rUnder; · subst j5; simp [Fin.ext_iff, hU]
        simp [j1, j2, j3, j4, j5]
      · simp only [geSubCost]
        rw [hS3, hS2t2]; dsimp only; rw [hbor]
        simp only [Bool.false_eq_true, ↓reduceIte, subDecideCost,
          Function.update_of_ne (by decide : rUnder ≠ rDiff),
          Function.update_of_ne (by decide : rUnder ≠ rCarry),
          Function.update_of_ne (by decide : rUnder ≠ rTmp1),
          Function.update_of_ne (by decide : rUnder ≠ rRem), hU,
          Function.update_of_ne (by decide : rCarry ≠ rUnder),
          Function.update_of_ne (by decide : rCarry ≠ rDiff), Function.update_self,
          subCommitCost, clearExec, stripFalseExec_eq,
          Function.update_of_ne (by decide : rDiff ≠ rTmp1),
          Function.update_of_ne (by decide : rDiff ≠ rCarry),
          Function.update_of_ne (by decide : rDiff ≠ rUnder),
          Function.update_of_ne (by decide : rTmp1 ≠ rCarry),
          Function.update_of_ne (by decide : rTmp1 ≠ rUnder),
          Function.update_of_ne (by decide : rTmp1 ≠ rDiff)]
        have hdlen : ((subBitsAux rem.bits b.bits false).1.reverse.dropWhile (fun x => !x)).length ≤
            (subBitsAux rem.bits b.bits false).1.reverse.length := (List.dropWhile_suffix _).length_le
        simp only [List.length_reverse, hsub.1, List.length_drop] at hdlen hcost2 ⊢
        change ((3 * ((subBitsAux rem.bits b.bits false).1.reverse.dropWhile (fun x => !x)).length + 1) +
            ((2 * rem.bits.length + 3) + (3 * rem.bits.length + 1)) + 2) + 2 + _ ≤ _
        omega
    ·
      have hltb : rem < b := by
        rw [hbor] at hsub
        have hlt2 := ofBits_lt_two_pow (subBitsAux rem.bits b.bits false).1
        rw [hsub.1] at hlt2
        simp at hsub
        omega
      have hmod : rem % b = rem := Nat.mod_eq_of_lt hltb
      refine ⟨?_, ?_⟩
      · simp only [geSubExec]
        rw [hS3]; dsimp only; rw [hbor]
        simp only [↓reduceIte, subDecideExec,
          Function.update_of_ne (by decide : rUnder ≠ rDiff),
          Function.update_of_ne (by decide : rUnder ≠ rCarry),
          Function.update_of_ne (by decide : rUnder ≠ rTmp1),
          Function.update_of_ne (by decide : rUnder ≠ rRem), hU,
          Function.update_of_ne (by decide : rCarry ≠ rUnder),
          Function.update_of_ne (by decide : rCarry ≠ rDiff), Function.update_self,
          subAbortExec, clearExec, revMoveExec]
        funext j
        by_cases j1 : j = rRem; · subst j1; simp [Fin.ext_iff, hmod]
        by_cases j2 : j = rTmp1; · subst j2; simp [Fin.ext_iff, h1]
        by_cases j3 : j = rDiff; · subst j3; simp [Fin.ext_iff, hD]
        by_cases j4 : j = rCarry; · subst j4; simp [Fin.ext_iff, hC]
        by_cases j5 : j = rUnder; · subst j5; simp [Fin.ext_iff, hU]
        simp [j1, j2, j3, j4, j5]
      · simp only [geSubCost]
        rw [hS3, hS2t2]; dsimp only; rw [hbor]
        simp only [↓reduceIte, subDecideCost,
          Function.update_of_ne (by decide : rUnder ≠ rDiff),
          Function.update_of_ne (by decide : rUnder ≠ rCarry),
          Function.update_of_ne (by decide : rUnder ≠ rTmp1),
          Function.update_of_ne (by decide : rUnder ≠ rRem), hU,
          Function.update_of_ne (by decide : rCarry ≠ rUnder),
          Function.update_of_ne (by decide : rCarry ≠ rDiff), Function.update_self,
          subAbortCost, clearExec,
          Function.update_of_ne (by decide : rTmp1 ≠ rDiff),
          Function.update_of_ne (by decide : rTmp1 ≠ rCarry),
          Function.update_of_ne (by decide : rTmp1 ≠ rUnder),
          Function.update_of_ne (by decide : rDiff ≠ rCarry),
          Function.update_of_ne (by decide : rDiff ≠ rUnder),
          Function.update_of_ne (by decide : rCarry ≠ rUnder),
          Function.update_of_ne (by decide : rUnder ≠ rTmp1),
          Function.update_of_ne (by decide : rUnder ≠ rDiff),
          Function.update_of_ne (by decide : rUnder ≠ rCarry)]
        simp only [List.length_reverse, hsub.1, List.length_drop, List.length_nil] at hcost2 ⊢
        change ((3 * rem.bits.length + 1) +
            ((3 * rem.bits.length + 1) + ((3 * 0 + 1) + (3 * 0 + 1))) + 3) + 2 + _ ≤ _
        omega
  ·
    have hltLen : rem.bits.length < b.bits.length := by omega
    have hltb : rem < b := by
      have h1 := ofBits_lt_two_pow rem.bits
      rw [ofBits_bits] at h1
      have h2 := bits_ge_two_pow hb
      have h3 : 2 ^ rem.bits.length ≤ 2 ^ (b.bits.length - 1) :=
        Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      omega
    have hmod : rem % b = rem := Nat.mod_eq_of_lt hltb
    have hpass1_under : ∀ (lb la : List Bool) (bor : Bool) (U : RK → List Bool),
        la.length < lb.length → U rRem = la → U rCarry = (if bor then [true] else []) →
        ∃ (d c : List Bool), d.length ≤ la.length ∧ c.length ≤ 1 ∧
          lb.foldl (fun W bb => subPass1Step bb W) U =
            Function.update (Function.update (Function.update (Function.update (Function.update
              (Function.update U rRem []) rTmp2 (lb.reverse ++ U rTmp2))
              rTmp1 (la.reverse ++ U rTmp1)) rCarry c) rDiff (d ++ U rDiff))
              rUnder (List.replicate (lb.length - la.length) true ++ U rUnder) := by
      intro lb
      induction lb with
      | nil => intro la _ _ h; simp at h
      | cons bb lb ih =>
        intro la bor U hlen hUR hUC
        cases la with
        | nil =>
          simp only [List.foldl_cons]
          have hst : subPass1Step bb U =
              Function.update (Function.update (Function.update U rTmp2 (bb :: U rTmp2))
                rRem []) rUnder (true :: U rUnder) := by
            funext j; simp only [subPass1Step, hUR, Function.update_of_ne (by decide : rRem ≠ rTmp2)]
            by_cases j1 : j = rUnder; · subst j1; simp [Fin.ext_iff]
            by_cases j2 : j = rRem; · subst j2; simp [Fin.ext_iff]
            by_cases j3 : j = rTmp2; · subst j3; simp [Fin.ext_iff]
            simp [j1, j2, j3]
          have hrest : ∀ (lb' : List Bool) (W : RK → List Bool), W rRem = [] →
              lb'.foldl (fun Z x => subPass1Step x Z) W =
                Function.update (Function.update W rTmp2 (lb'.reverse ++ W rTmp2))
                  rUnder (List.replicate lb'.length true ++ W rUnder) := by
            intro lb'
            induction lb' with
            | nil => intro W _; simp [Function.update_eq_self]
            | cons x lb' ih' =>
              intro W hWR
              simp only [List.foldl_cons]
              have hs : subPass1Step x W =
                  Function.update (Function.update W rTmp2 (x :: W rTmp2)) rUnder (true :: W rUnder) := by
                funext j; simp only [subPass1Step, hWR, Function.update_of_ne (by decide : rRem ≠ rTmp2)]
                by_cases j1 : j = rUnder; · subst j1; simp [Fin.ext_iff]
                by_cases j2 : j = rRem; · subst j2; simp [Fin.ext_iff, hWR]
                by_cases j3 : j = rTmp2; · subst j3; simp [Fin.ext_iff]
                simp [j1, j2, j3]
              rw [hs, ih' _ (by simp [Fin.ext_iff, hWR])]
              funext j; simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
                List.length_cons, List.replicate_succ]
              by_cases j1 : j = rUnder; · subst j1; simp [Fin.ext_iff, replicate_append_cons]
              by_cases j2 : j = rTmp2; · subst j2; simp [Fin.ext_iff]
              simp [j1, j2]
          rw [hst, hrest lb _ (by simp [Fin.ext_iff])]
          refine ⟨[], if bor then [true] else [], by decide, by cases bor <;> decide, ?_⟩
          funext j
          simp only [List.length_cons, List.length_nil, Nat.sub_zero, List.replicate_succ,
            List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append]
          by_cases j1 : j = rUnder; · subst j1; simp [Fin.ext_iff, replicate_append_cons]
          by_cases j2 : j = rDiff; · subst j2; simp [Fin.ext_iff]
          by_cases j3 : j = rCarry; · subst j3; simp [Fin.ext_iff, hUC]
          by_cases j4 : j = rTmp1; · subst j4; simp [Fin.ext_iff]
          by_cases j5 : j = rTmp2; · subst j5; simp [Fin.ext_iff]
          by_cases j6 : j = rRem; · subst j6; simp [Fin.ext_iff]
          simp [j1, j2, j3, j4, j5, j6]
        | cons a la =>
          simp only [List.length_cons] at hlen
          simp only [List.foldl_cons]
          have hst : subPass1Step bb U =
              Function.update (Function.update (Function.update (Function.update (Function.update U
                rRem la) rTmp2 (bb :: U rTmp2)) rTmp1 (a :: U rTmp1))
                rCarry (if fullSubBor a bb bor then [true] else []))
                rDiff (fullSubDiff a bb bor :: U rDiff) := subPass1Step_cons_eq bb a la bor U hUR hUC
          obtain ⟨d, c, hd, hc, hrec⟩ := ih la (fullSubBor a bb bor) (subPass1Step bb U)
            (by omega) (by rw [hst]; simp [Fin.ext_iff]) (by rw [hst]; simp [Fin.ext_iff])
          refine ⟨d ++ [fullSubDiff a bb bor], c, by simp; omega, hc, ?_⟩
          rw [hrec, hst]
          funext j
          simp only [List.length_cons, Nat.succ_sub_succ_eq_sub, List.reverse_cons,
            List.append_assoc, List.singleton_append]
          by_cases j1 : j = rUnder; · subst j1; simp [Fin.ext_iff]
          by_cases j2 : j = rDiff; · subst j2; simp [Fin.ext_iff]
          by_cases j3 : j = rCarry; · subst j3; simp [Fin.ext_iff]
          by_cases j4 : j = rTmp1; · subst j4; simp [Fin.ext_iff]
          by_cases j5 : j = rTmp2; · subst j5; simp [Fin.ext_iff]
          by_cases j6 : j = rRem; · subst j6; simp [Fin.ext_iff]
          simp [j1, j2, j3, j4, j5, j6]
    obtain ⟨d, c, hd, hc, hS1'⟩ := hpass1_under b.bits rem.bits false (Function.update S rF0 [])
      hltLen (by simp [Fin.ext_iff, hRem]) (by simp [Fin.ext_iff, hC])
    have hS1 : (S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 []) =
        Function.update (Function.update (Function.update (Function.update (Function.update
          (Function.update (Function.update S rF0 []) rRem []) rTmp2 b.bits.reverse)
          rTmp1 rem.bits.reverse) rCarry c) rDiff d)
          rUnder (List.replicate (b.bits.length - rem.bits.length) true) := by
      rw [hF0, hS1']
      funext j
      by_cases j1 : j = rUnder; · subst j1; simp [Fin.ext_iff, hU]
      by_cases j2 : j = rDiff; · subst j2; simp [Fin.ext_iff, hD]
      by_cases j3 : j = rCarry; · subst j3; simp [Fin.ext_iff]
      by_cases j4 : j = rTmp1; · subst j4; simp [Fin.ext_iff, h1]
      by_cases j5 : j = rTmp2; · subst j5; simp [Fin.ext_iff, h2]
      by_cases j6 : j = rRem; · subst j6; simp [Fin.ext_iff]
      by_cases j7 : j = rF0; · subst j7; simp [Fin.ext_iff]
      simp [j1, j2, j3, j4, j5, j6, j7]
    have hS1Rem : ((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem = [] := by
      rw [hS1]; simp [Fin.ext_iff]
    have hS3 : revMoveExec rTmp2 rF0
        (((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem |>.foldl
          (fun U rb => subStepCarry rb false U)
          (Function.update ((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem [])) =
        Function.update (Function.update (Function.update (Function.update (Function.update S
          rRem []) rTmp1 rem.bits.reverse) rCarry c) rDiff d)
          rUnder (List.replicate (b.bits.length - rem.bits.length) true) := by
      rw [hS1Rem, List.foldl_nil, hS1]
      funext j; simp only [revMoveExec]
      by_cases j1 : j = rF0; · subst j1; simp [Fin.ext_iff, hF0]
      by_cases j2 : j = rTmp2; · subst j2; simp [Fin.ext_iff, h2]
      by_cases j3 : j = rUnder; · subst j3; simp [Fin.ext_iff]
      by_cases j4 : j = rDiff; · subst j4; simp [Fin.ext_iff]
      by_cases j5 : j = rCarry; · subst j5; simp [Fin.ext_iff]
      by_cases j6 : j = rTmp1; · subst j6; simp [Fin.ext_iff]
      by_cases j7 : j = rRem; · subst j7; simp [Fin.ext_iff]
      simp [j1, j2, j3, j4, j5, j6, j7]
    obtain ⟨u, hu⟩ : ∃ u, b.bits.length - rem.bits.length = u + 1 := ⟨b.bits.length - rem.bits.length - 1, by omega⟩
    refine ⟨?_, ?_⟩
    · simp only [geSubExec]
      rw [hS3, hu, List.replicate_succ]
      simp only [subDecideExec, Function.update_self, subAbortExec, clearExec, revMoveExec]
      funext j
      by_cases j1 : j = rRem; · subst j1; simp [Fin.ext_iff, hmod]
      by_cases j2 : j = rTmp1; · subst j2; simp [Fin.ext_iff, h1]
      by_cases j3 : j = rDiff; · subst j3; simp [Fin.ext_iff, hD]
      by_cases j4 : j = rCarry; · subst j4; simp [Fin.ext_iff, hC]
      by_cases j5 : j = rUnder; · subst j5; simp [Fin.ext_iff, hU]
      simp [j1, j2, j3, j4, j5]
    · have hcost1 : forEachCost rF0 (fun bb => subPass1Step bb) (fun _ _ => 10) (S rF0) S ≤
          12 * b.bits.length + 1 := by
        have hfl : (S rF0).length = b.bits.length := by rw [hF0]
        have := forEachCost_le rF0 (fun bb => subPass1Step bb) (fun _ _ => 10) (fun _ => True) 10
          (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial) (S rF0) S trivial
        rw [hfl] at this; omega
      have hS2t2 : (((((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem).foldl
          (fun U rb => subStepCarry rb false U)
          (Function.update ((S rF0).foldl (fun U bb => subPass1Step bb U) (Function.update S rF0 [])) rRem [])) rTmp2).length =
          b.bits.length := by
        rw [hS1Rem, List.foldl_nil, hS1]; simp [Fin.ext_iff]
      simp only [geSubCost]
      rw [hS3, hS2t2, hS1Rem, hu, List.replicate_succ]
      simp only [forEachCost, subDecideCost, Function.update_self, subAbortCost, clearExec,
        Function.update_of_ne (by decide : rTmp1 ≠ rDiff),
        Function.update_of_ne (by decide : rTmp1 ≠ rCarry),
        Function.update_of_ne (by decide : rTmp1 ≠ rUnder),
        Function.update_of_ne (by decide : rDiff ≠ rCarry),
        Function.update_of_ne (by decide : rCarry ≠ rDiff),
        Function.update_of_ne (by decide : rDiff ≠ rUnder),
        Function.update_of_ne (by decide : rCarry ≠ rUnder),
        List.length_reverse, List.length_replicate]
      omega

def divStepExec (bit : Bool) (S : RK → List Bool) : RK → List Bool :=
  geSubExec (shiftBitExec bit S)

def divStepCost (bit : Bool) (S : RK → List Bool) : ℕ :=
  geSubCost (shiftBitExec bit S) + 5

theorem psb_divStep (bit : Bool) : PureSB (divStepExec bit) (divStepCost bit) := by
  unfold divStepExec divStepCost
  exact psb_seq (psb_shiftBit bit) psb_geSub

theorem indep_divStep (bit : Bool) : Indep rRrev (divStepExec bit) := by
  unfold divStepExec
  exact indep_seq (indep_shiftBit bit) indep_geSub

def modFibExec (S : RK → List Bool) : RK → List Bool :=
  let S1 := revMoveExec rIn rRrev S
  let S2 := (S1 rRrev).foldl (fun U bit => divStepExec bit U) (Function.update S1 rRrev [])
  let S3 := clearExec rF0 S2
  let S4 := revMoveExec rRem rTmp1 S3
  revMoveExec rTmp1 rOut S4

def modFibCost (S : RK → List Bool) : ℕ :=
  let S1 := revMoveExec rIn rRrev S
  let S2 := (S1 rRrev).foldl (fun U bit => divStepExec bit U) (Function.update S1 rRrev [])
  let S3 := clearExec rF0 S2
  let S4 := revMoveExec rRem rTmp1 S3
  (3 * (S4 rTmp1).length + 1) +
    ((3 * (S3 rRem).length + 1) +
      ((3 * (S2 rF0).length + 1) +
        (forEachCost rRrev divStepExec divStepCost (S1 rRrev) S1 +
          (3 * (S rIn).length + 1))))

theorem psb_modFib : PureSB modFibExec modFibCost := by
  unfold modFibExec modFibCost
  exact psb_seq
    (psb_seq
      (psb_seq
        (psb_seq (psb_revMove (a := rIn) (b := rRrev) (by decide))
          (psb_forEach rRrev (B := divStepCost) (psb_divStep false) (psb_divStep true) indep_divStep))
        (psb_clear rF0))
      (psb_revMove (a := rRem) (b := rTmp1) (by decide)))
    (psb_revMove (a := rTmp1) (b := rOut) (by decide))

theorem foldl_mod_ofBits (b : ℕ) (r : List Bool) :
    r.reverse.foldl (fun acc bit => (2 * acc + bit.toNat) % b) 0 = ofBits r % b := by
  induction r with
  | nil => simp [ofBits]
  | cons bit r ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, ofBits]
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm]

theorem modFib_spec (S : RK → List Bool) (b : ℕ) (hb : 0 < b)
    (hF0 : S rF0 = b.bits) (hRem : S rRem = []) (hRrev : S rRrev = []) (hOut : S rOut = [])
    (hD : S rDiff = []) (h1 : S rTmp1 = []) (h2 : S rTmp2 = []) (hC : S rCarry = []) (hU : S rUnder = []) :
    modFibExec S = Function.update (Function.update (Function.update S rIn []) rF0 []) rOut (ofBits (S rIn) % b).bits ∧
    modFibCost S ≤ (S rIn).length * (40 * b.bits.length + 55) + 10 * b.bits.length + 10 := by
  have hfold : ∀ (l : List Bool) (acc : ℕ) (U : RK → List Bool),
      acc < b → U rF0 = b.bits → U rRem = acc.bits →
      U rDiff = [] → U rTmp1 = [] → U rTmp2 = [] → U rCarry = [] → U rUnder = [] →
      l.foldl (fun W bit => divStepExec bit W) U =
        Function.update U rRem (l.foldl (fun a bit => (2 * a + bit.toNat) % b) acc).bits ∧
      forEachCost rRrev divStepExec divStepCost l U ≤
        l.length * (40 * b.bits.length + 52) + 1 := by
    intro l
    induction l with
    | nil =>
      intro acc U _ _ hUR _ _ _ _ _
      exact ⟨by simp [hUR, Function.update_eq_self], by simp [forEachCost]⟩
    | cons bit l ih =>
      intro acc U hacc hUF0 hUR hUD hU1 hU2 hUC hUU
      simp only [List.foldl_cons, forEachCost, List.length_cons]
      have hsh1 : shiftBitExec bit U = Function.update U rRem (2 * acc + bit.toNat).bits :=
        shiftBitExec_bits bit acc U hUR
      have hsh2 : shiftBitExec bit (Function.update U rRrev l) =
          Function.update (Function.update U rRrev l) rRem (2 * acc + bit.toNat).bits :=
        shiftBitExec_bits bit acc _ (by simp [Fin.ext_iff, hUR])
      have hlt2 : 2 * acc + bit.toNat < 2 * b := by cases bit <;> simp <;> omega
      have hge1 := geSub_spec (shiftBitExec bit U) (2 * acc + bit.toNat) b hb hlt2
        (by rw [hsh1]; simp) (by rw [hsh1]; simp [Fin.ext_iff, hUF0]) (by rw [hsh1]; simp [Fin.ext_iff, hUD])
        (by rw [hsh1]; simp [Fin.ext_iff, hU1]) (by rw [hsh1]; simp [Fin.ext_iff, hU2]) (by rw [hsh1]; simp [Fin.ext_iff, hUC])
        (by rw [hsh1]; simp [Fin.ext_iff, hUU])
      have hge2 := geSub_spec (shiftBitExec bit (Function.update U rRrev l)) (2 * acc + bit.toNat) b hb hlt2
        (by rw [hsh2]; simp) (by rw [hsh2]; simp [Fin.ext_iff, hUF0]) (by rw [hsh2]; simp [Fin.ext_iff, hUD])
        (by rw [hsh2]; simp [Fin.ext_iff, hU1]) (by rw [hsh2]; simp [Fin.ext_iff, hU2]) (by rw [hsh2]; simp [Fin.ext_iff, hUC])
        (by rw [hsh2]; simp [Fin.ext_iff, hUU])
      have hdiv1 : divStepExec bit U = Function.update U rRem ((2 * acc + bit.toNat) % b).bits := by
        simp only [divStepExec]; rw [hge1.1, hsh1, Function.update_idem]
      have hdiv2 : divStepExec bit (Function.update U rRrev l) =
          Function.update (Function.update U rRrev l) rRem ((2 * acc + bit.toNat) % b).bits := by
        simp only [divStepExec]; rw [hge2.1, hsh2, Function.update_idem]
      have hacc' : (2 * acc + bit.toNat) % b < b := Nat.mod_lt _ hb
      have hrec1 := ih ((2 * acc + bit.toNat) % b) (divStepExec bit U) hacc'
        (by rw [hdiv1]; simp [Fin.ext_iff, hUF0]) (by rw [hdiv1]; simp) (by rw [hdiv1]; simp [Fin.ext_iff, hUD])
        (by rw [hdiv1]; simp [Fin.ext_iff, hU1]) (by rw [hdiv1]; simp [Fin.ext_iff, hU2]) (by rw [hdiv1]; simp [Fin.ext_iff, hUC])
        (by rw [hdiv1]; simp [Fin.ext_iff, hUU])
      have hrec2 := ih ((2 * acc + bit.toNat) % b) (divStepExec bit (Function.update U rRrev l)) hacc'
        (by rw [hdiv2]; simp [Fin.ext_iff, hUF0]) (by rw [hdiv2]; simp) (by rw [hdiv2]; simp [Fin.ext_iff, hUD])
        (by rw [hdiv2]; simp [Fin.ext_iff, hU1]) (by rw [hdiv2]; simp [Fin.ext_iff, hU2]) (by rw [hdiv2]; simp [Fin.ext_iff, hUC])
        (by rw [hdiv2]; simp [Fin.ext_iff, hUU])
      refine ⟨?_, ?_⟩
      · rw [hrec1.1, hdiv1, Function.update_idem]
      · have hdc : divStepCost bit (Function.update U rRrev l) ≤ 40 * b.bits.length + 50 := by
          simp only [divStepCost]; have := hge2.2; omega
        have hrc := hrec2.2
        have hmul : (l.length + 1) * (40 * b.bits.length + 52) =
            l.length * (40 * b.bits.length + 52) + (40 * b.bits.length + 52) := by ring
        omega
  have hS1R : (revMoveExec rIn rRrev S) rRrev = (S rIn).reverse := by simp [Fin.ext_iff, revMoveExec, hRrev]
  have hf1 := hfold (S rIn).reverse 0 (Function.update (revMoveExec rIn rRrev S) rRrev []) hb
    (by simp [Fin.ext_iff, revMoveExec, hF0]) (by simp [Fin.ext_iff, revMoveExec, hRem]) (by simp [Fin.ext_iff, revMoveExec, hD])
    (by simp [Fin.ext_iff, revMoveExec, h1]) (by simp [Fin.ext_iff, revMoveExec, h2]) (by simp [Fin.ext_iff, revMoveExec, hC])
    (by simp [Fin.ext_iff, revMoveExec, hU])
  have hf2 := hfold (S rIn).reverse 0 (revMoveExec rIn rRrev S) hb
    (by simp [Fin.ext_iff, revMoveExec, hF0]) (by simp [Fin.ext_iff, revMoveExec, hRem]) (by simp [Fin.ext_iff, revMoveExec, hD])
    (by simp [Fin.ext_iff, revMoveExec, h1]) (by simp [Fin.ext_iff, revMoveExec, h2]) (by simp [Fin.ext_iff, revMoveExec, hC])
    (by simp [Fin.ext_iff, revMoveExec, hU])
  refine ⟨?_, ?_⟩
  · simp only [modFibExec]
    rw [hS1R, hf1.1, foldl_mod_ofBits]
    simp only [clearExec, revMoveExec]
    funext j
    by_cases j1 : j = rOut; · subst j1; simp [Fin.ext_iff, hOut, h1]
    by_cases j2 : j = rTmp1; · subst j2; simp [Fin.ext_iff, h1]
    by_cases j3 : j = rRem; · subst j3; simp [Fin.ext_iff, hRem]
    by_cases j4 : j = rF0; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = rRrev; · subst j5; simp [Fin.ext_iff, hRrev]
    by_cases j6 : j = rIn; · subst j6; simp [Fin.ext_iff]
    simp [j1, j2, j3, j4, j5, j6]
  · simp only [modFibCost]
    rw [hS1R, hf1.1, foldl_mod_ofBits]
    have hrem_le : (ofBits (S rIn) % b).bits.length ≤ b.bits.length :=
      bits_length_mono (Nat.le_of_lt (Nat.mod_lt _ hb))
    have hfc := hf2.2
    rw [List.length_reverse] at hfc
    have hlenF0 : (Function.update (Function.update (revMoveExec rIn rRrev S) rRrev []) rRem
        (ofBits (S rIn) % b).bits rF0).length = b.bits.length := by
      simp [Fin.ext_iff, revMoveExec, hF0]
    have hlenRem : (clearExec rF0 (Function.update (Function.update (revMoveExec rIn rRrev S) rRrev []) rRem
        (ofBits (S rIn) % b).bits) rRem).length = (ofBits (S rIn) % b).bits.length := by
      simp [Fin.ext_iff, clearExec]
    have hlenTmp1 : (revMoveExec rRem rTmp1 (clearExec rF0 (Function.update (Function.update (revMoveExec rIn rRrev S) rRrev []) rRem
        (ofBits (S rIn) % b).bits)) rTmp1).length = (ofBits (S rIn) % b).bits.length := by
      simp [Fin.ext_iff, clearExec, revMoveExec, h1]
    rw [hlenF0, hlenRem, hlenTmp1]
    have hmul : (S rIn).length * (40 * b.bits.length + 55) =
        (S rIn).length * (40 * b.bits.length + 52) + 3 * (S rIn).length := by ring
    omega

def readExec (S : RK → List Bool) : RK → List Bool :=
  modFibExec (computeFibExec (computeLExec (computeTExec (doubleNExec (parseHeaderExec rIn rN S)))))

def readCost (S : RK → List Bool) : ℕ :=
  let S1 := parseHeaderExec rIn rN S
  let S2 := doubleNExec S1
  let S3 := computeTExec S2
  let S4 := computeLExec S3
  let S5 := computeFibExec S4
  modFibCost S5 + (computeFibCost S4 + (computeLCost S3 + (computeTCost S2 +
    ((4 * (S1 rN).length + 1) + (2 * (S rIn).length + 3)))))

theorem psb_read : PureSB readExec readCost := by
  unfold readExec readCost
  exact psb_seq (psb_seq (psb_seq (psb_seq (psb_seq (psb_parseHeader (inp := rIn) (N := rN) (by decide)) psb_doubleN)
    psb_computeT) psb_computeL) psb_computeFib) psb_modFib

def readFn (x : List Bool) : List Bool :=
  let n := (x.takeWhile id).length
  let r := (x.dropWhile id).tail
  let v := 2 * n
  let L := 2 * (1 + v * ((v + 1).log2 + 1))
  let b := Nat.fib (L + 2)
  (ofBits r % b).bits

theorem read_spec_all (x : List Bool) :
    let S0 := Function.update (fun _ : RK => ([] : List Bool)) rIn x
    readExec S0 = Function.update (fun _ : RK => ([] : List Bool)) rOut (readFn x) ∧
    1 + readCost S0 ≤ (Polynomial.C 5000 * (Polynomial.X + 1) ^ 5).eval x.length := by
  intro S0
  set n := (x.takeWhile id).length
  set r := (x.dropWhile id).tail
  set v := 2 * n
  set t := (v + 1).log2 + 1
  set L := 2 * (1 + v * t)
  set b := Nat.fib (L + 2)
  have hn_le : n ≤ x.length := (List.takeWhile_prefix _).length_le
  have hr_le : r.length ≤ x.length := by
    have h1 := (List.dropWhile_suffix (l := x) id).length_le
    simp only [r, List.length_tail]; omega
  have ht_le : t ≤ v + 1 := by
    have := bits_length_le (v + 1)
    rw [bits_length_eq_log2 (v + 1) (Nat.succ_pos v)] at this
    exact this
  have hS1 : parseHeaderExec rIn rN S0 =
      Function.update (Function.update S0 rIn r) rN (List.replicate n true) := by
    rw [parseHeaderExec_eq (by decide)]
    funext j
    by_cases j1 : j = rN; · subst j1; simp [Fin.ext_iff, S0, n]
    by_cases j2 : j = rIn; · subst j2; simp [Fin.ext_iff, S0, r]
    simp [j1, j2]
  have hS2 : doubleNExec (parseHeaderExec rIn rN S0) =
      Function.update (Function.update (Function.update S0 rIn r) rN []) rV (List.replicate v true) := by
    rw [hS1, doubleNExec_eq]
    funext j
    by_cases j1 : j = rV; · subst j1; simp [Fin.ext_iff, S0, v]
    by_cases j2 : j = rN; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = rIn; · subst j3; simp [Fin.ext_iff]
    simp [j1, j2, j3]
  have hT := computeT_spec (doubleNExec (parseHeaderExec rIn rN S0))
    (by rw [hS2]; simp [Fin.ext_iff, S0]) (by rw [hS2]; simp [Fin.ext_iff, S0]) (by rw [hS2]; simp [Fin.ext_iff, S0])
  have hS2V : (doubleNExec (parseHeaderExec rIn rN S0) rV).length = v := by rw [hS2]; simp
  have hS3 : computeTExec (doubleNExec (parseHeaderExec rIn rN S0)) =
      Function.update (Function.update (Function.update S0 rIn r) rV (List.replicate v true))
        rT (v + 1).bits := by
    rw [hT.1, hS2V, hS2]
    funext j
    by_cases j1 : j = rT; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = rV; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = rN; · subst j3; simp [Fin.ext_iff, S0]
    by_cases j4 : j = rIn; · subst j4; simp [Fin.ext_iff]
    simp [j1, j2, j3, j4]
  obtain ⟨lL, hlL, hS4', hC4⟩ := computeL_spec (computeTExec (doubleNExec (parseHeaderExec rIn rN S0)))
    (by rw [hS3]; simp [Fin.ext_iff, S0]) (by rw [hS3]; simp [Fin.ext_iff, S0])
  have hS3V : (computeTExec (doubleNExec (parseHeaderExec rIn rN S0)) rV).length = v := by
    rw [hS3]; simp [Fin.ext_iff]
  have hS3T : (computeTExec (doubleNExec (parseHeaderExec rIn rN S0)) rT).length = t := by
    rw [hS3]; simp [Fin.ext_iff, bits_length_eq_log2 (v + 1) (Nat.succ_pos v), t]
  have hlL_eq : lL.length = L + 2 := by
    rw [hlL, hS3V, hS3T]
    show 2 * v * t + 4 = 2 * (1 + v * t) + 2
    ring
  have hS4 : computeLExec (computeTExec (doubleNExec (parseHeaderExec rIn rN S0))) =
      Function.update (Function.update S0 rIn r) rL lL := by
    rw [hS4', hS3]
    funext j
    by_cases j1 : j = rL; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = rT; · subst j2; simp [Fin.ext_iff, S0]
    by_cases j3 : j = rV; · subst j3; simp [Fin.ext_iff, S0]
    by_cases j4 : j = rIn; · subst j4; simp [Fin.ext_iff]
    simp [j1, j2, j3, j4]
  have hFib := computeFib_spec (computeLExec (computeTExec (doubleNExec (parseHeaderExec rIn rN S0))))
    (by rw [hS4]; simp [Fin.ext_iff, S0]) (by rw [hS4]; simp [Fin.ext_iff, S0]) (by rw [hS4]; simp [Fin.ext_iff, S0])
    (by rw [hS4]; simp [Fin.ext_iff, S0]) (by rw [hS4]; simp [Fin.ext_iff, S0])
  have hS4L : (computeLExec (computeTExec (doubleNExec (parseHeaderExec rIn rN S0))) rL).length = L + 2 := by
    rw [hS4]; simp [hlL_eq]
  have hS5 : computeFibExec (computeLExec (computeTExec (doubleNExec (parseHeaderExec rIn rN S0)))) =
      Function.update (Function.update S0 rIn r) rF0 b.bits := by
    rw [hFib.1, hS4L, hS4]
    funext j
    by_cases j1 : j = rF0; · subst j1; simp [b]
    by_cases j2 : j = rL; · subst j2; simp [Fin.ext_iff, S0]
    by_cases j3 : j = rIn; · subst j3; simp [Fin.ext_iff]
    simp [j1, j2, j3]
  have hb_pos : 0 < b := by
    have h4 : 4 ≤ L + 2 := by omega
    have hmono : Nat.fib 4 ≤ Nat.fib (L + 2) := Nat.fib_mono h4
    have : Nat.fib 4 = 3 := by decide
    omega
  have hMod := modFib_spec (computeFibExec (computeLExec (computeTExec (doubleNExec (parseHeaderExec rIn rN S0)))))
    b hb_pos (by rw [hS5]; simp) (by rw [hS5]; simp [Fin.ext_iff, S0]) (by rw [hS5]; simp [Fin.ext_iff, S0])
    (by rw [hS5]; simp [Fin.ext_iff, S0]) (by rw [hS5]; simp [Fin.ext_iff, S0]) (by rw [hS5]; simp [Fin.ext_iff, S0])
    (by rw [hS5]; simp [Fin.ext_iff, S0]) (by rw [hS5]; simp [Fin.ext_iff, S0]) (by rw [hS5]; simp [Fin.ext_iff, S0])
  refine ⟨?_, ?_⟩
  · simp only [readExec]
    rw [hMod.1, hS5]
    funext j
    by_cases j1 : j = rOut; · subst j1; simp [Fin.ext_iff, readFn, n, r, v, t, L, b]
    by_cases j2 : j = rF0; · subst j2; simp [Fin.ext_iff, S0]
    by_cases j3 : j = rIn; · subst j3; simp [Fin.ext_iff, S0]
    simp [j1, j2, j3, S0]
  · simp only [readCost, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have hC3 := hT.2; rw [hS2V] at hC3
    rw [hS3V, hS3T] at hC4
    have hC5 := hFib.2; rw [hS4L] at hC5
    have hS5In : (computeFibExec (computeLExec (computeTExec (doubleNExec (parseHeaderExec rIn rN S0)))) rIn).length = r.length := by
      rw [hS5]; simp [Fin.ext_iff]
    have hC6 := hMod.2; rw [hS5In] at hC6
    have hS1N : (parseHeaderExec rIn rN S0 rN).length = n := by rw [hS1]; simp
    have hS0In : (S0 rIn).length = x.length := by simp [S0]
    rw [hS1N, hS0In]
    have hblen : b.bits.length ≤ L + 2 := fib_bits_length_le (L + 2)
    set N := x.length + 1
    have hN1 : 1 ≤ N := by omega
    have hN2 : N ≤ N ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right N (by omega)
    have hN3 : N ^ 2 ≤ N ^ 3 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hN4 : N ^ 3 ≤ N ^ 4 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hN5 : N ^ 4 ≤ N ^ 5 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
    have h1_N2 : 1 ≤ N ^ 2 := le_trans hN1 hN2
    have h1_N5 : 1 ≤ N ^ 5 := le_trans h1_N2 (le_trans hN3 (le_trans hN4 hN5))
    have hN_N5 : N ≤ N ^ 5 := le_trans hN2 (le_trans hN3 (le_trans hN4 hN5))
    have hN2_N5 : N ^ 2 ≤ N ^ 5 := le_trans hN3 (le_trans hN4 hN5)
    have hN3_N5 : N ^ 3 ≤ N ^ 5 := le_trans hN4 hN5
    have hvN : v ≤ 2 * N := by omega
    have htN : t ≤ 2 * N := by omega
    have hvt : v * t ≤ 4 * N ^ 2 := by
      calc v * t ≤ (2 * N) * (2 * N) := Nat.mul_le_mul hvN htN
        _ = 4 * N ^ 2 := by ring
    have hL3 : L + 3 ≤ 13 * N ^ 2 := by
      have : L + 3 = 2 * (v * t) + 5 := by show 2 * (1 + v * t) + 3 = 2 * (v * t) + 5; omega
      omega
    have hLsq : (L + 2 + 1) ^ 2 ≤ 169 * N ^ 4 := by
      calc (L + 2 + 1) ^ 2 = (L + 3) ^ 2 := by ring
        _ ≤ (13 * N ^ 2) ^ 2 := Nat.pow_le_pow_left hL3 2
        _ = 169 * N ^ 4 := by ring
    have hv1sq : (v + 1) ^ 2 ≤ 9 * N ^ 2 := by
      have hv1 : v + 1 ≤ 3 * N := by omega
      calc (v + 1) ^ 2 ≤ (3 * N) ^ 2 := Nat.pow_le_pow_left hv1 2
        _ = 9 * N ^ 2 := by ring
    have h16vt : 16 * v * t ≤ 64 * N ^ 2 := by
      calc 16 * v * t = 16 * (v * t) := by ring
        _ ≤ 16 * (4 * N ^ 2) := Nat.mul_le_mul_left 16 hvt
        _ = 64 * N ^ 2 := by ring
    have h6' : r.length * (40 * b.bits.length + 55) ≤ 520 * N ^ 3 + 55 * N := by
      calc r.length * (40 * b.bits.length + 55)
          ≤ N * (40 * (13 * N ^ 2) + 55) := Nat.mul_le_mul (by omega) (by omega)
        _ = 520 * N ^ 3 + 55 * N := by ring
    omega

theorem read_fast :
    ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) readFn,
      ∀ i, Finite (M.tm.Γ i) :=
  psb_to_polyTime rIn rOut psb_read readFn (Polynomial.C 5000 * (Polynomial.X + 1) ^ 5)
    (fun x => (read_spec_all x).1) (fun x => (read_spec_all x).2)

theorem readFn_on_valid (n Z : ℕ) :
    let v := 2 * n
    let L := 2 * (1 + v * ((v + 1).log2 + 1))
    let b := Nat.fib (L + 2)
    readFn (List.replicate n true ++ [false] ++ Z.bits) = (Z % b).bits := by
  intro v L b
  have htw : (List.replicate n true ++ [false] ++ Z.bits).takeWhile id = List.replicate n true := by
    rw [List.append_assoc, List.singleton_append]
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  have hdw : ((List.replicate n true ++ [false] ++ Z.bits).dropWhile id).tail = Z.bits := by
    rw [List.append_assoc, List.singleton_append]
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  simp only [readFn, htw, hdw, List.length_replicate, ofBits_bits]; rfl

end PEqualNP.Outside.L_meta_32063.ReadM


namespace PEqualNP.Outside.L_meta_32063.WriteM

open PEqualNP.Outside.L_meta_32063.Sim
open PEqualNP.Outside.L_meta_32063.ReadM

def fieldBits (w z : ℕ) : List Bool :=
  (List.range w).map (fun h => z.testBit h)

theorem fieldBits_length (w z : ℕ) : (fieldBits w z).length = w := by
  simp [fieldBits]

theorem fieldBits_zero (w : ℕ) : fieldBits w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [fieldBits, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      Nat.zero_testBit, List.replicate_succ]
    have h0 : (List.range w).map (fun _ => false) = fieldBits w 0 := by
      simp only [fieldBits, Nat.zero_testBit]
    rw [h0, ih]
    simpa using replicate_append_cons false [] w

theorem fieldBits_succ (w z : ℕ) :
    fieldBits (w + 1) z = z.testBit 0 :: fieldBits w (z / 2) := by
  unfold fieldBits
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro h _
  show z.testBit (h + 1) = (z / 2).testBit h
  rw [Nat.testBit_succ]

theorem incFixedBits_fieldBits : ∀ (w z : ℕ), incFixedBits (fieldBits w z) = fieldBits w (z + 1)
  | 0, _ => rfl
  | w + 1, z => by
    rw [fieldBits_succ, fieldBits_succ]
    cases hz : z.testBit 0
    · have hmod : z % 2 = 0 := by
        rw [Nat.testBit_zero] at hz; simp at hz; omega
      have hz1 : (z + 1).testBit 0 = true := by rw [Nat.testBit_zero]; simp; omega
      have hdiv : (z + 1) / 2 = z / 2 := by omega
      rw [incFixedBits, hz1, hdiv]
    · have hmod : z % 2 = 1 := by
        rw [Nat.testBit_zero] at hz; simp at hz; omega
      have hz1 : (z + 1).testBit 0 = false := by rw [Nat.testBit_zero]; simp; omega
      have hdiv : (z + 1) / 2 = z / 2 + 1 := by omega
      rw [incFixedBits, incFixedBits_fieldBits w (z / 2), hz1, hdiv]

theorem incFixedBits_len : ∀ l : List Bool, (incFixedBits l).length = l.length
  | [] => rfl
  | false :: _ => rfl
  | true :: l => by simp [incFixedBits, incFixedBits_len l]

def emitPairBits (w x y : ℕ) : List Bool :=
  fieldBits w x ++ fieldBits w y

def emitRange (w x y m : ℕ) : List Bool :=
  (List.range m).flatMap (fun d => emitPairBits w x (y + d))

theorem emitRange_zero (w x y : ℕ) : emitRange w x y 0 = [] := rfl

theorem emitRange_succ_front (w x y m : ℕ) :
    emitRange w x y (m + 1) = emitPairBits w x y ++ emitRange w x (y + 1) m := by
  unfold emitRange
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_zero]
  congr 1
  apply List.flatMap_congr
  intro d _
  show emitPairBits w x (y + (d + 1)) = emitPairBits w x (y + 1 + d)
  rw [show y + (d + 1) = y + 1 + d by omega]

theorem emitRange_add (w x y m1 m2 : ℕ) :
    emitRange w x y (m1 + m2) = emitRange w x y m1 ++ emitRange w x (y + m1) m2 := by
  induction m1 generalizing y with
  | zero => simp [emitRange_zero]
  | succ m1 ih =>
    rw [show m1 + 1 + m2 = (m1 + m2) + 1 by omega, emitRange_succ_front, emitRange_succ_front,
        ih (y + 1), List.append_assoc, show y + 1 + m1 = y + (m1 + 1) by omega]

def emitNoBase (w x remR remAll L1 : ℕ) : List Bool :=
  (if remR = 0 then [] else emitRange w x (x + 2) (remR - 1)) ++
    emitRange w x (x + 1 + remR) (remAll * L1)

def emitRow (w x y L : ℕ) : List Bool → List Bool
  | [] => []
  | b :: bs =>
    (if b then [] else emitPairBits w x y) ++ emitRange w x (y + 1) L ++
      emitRow w x (y + (L + 1)) L bs

def emitLeftRx0 (w x L remLeft : ℕ) (row : List Bool) : List Bool :=
  emitRange w x (x + 2) (L - 1) ++
    emitRange w x (x + L + 1) (remLeft * (L + 1)) ++
    emitRow w x (x + L + 1 + remLeft * (L + 1)) L row

def emitNoBaseLoop (w x remAll L1 : ℕ) : ℕ → List Bool
  | 0 => []
  | r + 1 =>
    emitNoBase w x r remAll L1 ++ emitNoBaseLoop w (x + 1) remAll L1 r

def emitLeftBlocks (w L : ℕ) (n : ℕ) : ℕ → ℕ → ℕ → List Bool → List Bool
  | 0, _, _, _ => []
  | m + 1, x, remAll, a =>
    let row := (List.range n).map (fun i => a.getD i false)
    let remLeft := m
    let remAll' := remAll - 1
    emitLeftRx0 w x L remLeft row ++
      emitNoBaseLoop w (x + 1) remAll' (L + 1) L ++
      emitLeftBlocks w L n m (x + L + 1) remAll' (a.drop n)

def emitRightBlocks (w L : ℕ) : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | m + 1, x, remAll =>
    let remAll' := remAll - 1
    emitNoBaseLoop w x remAll' (L + 1) (L + 1) ++
      emitRightBlocks w L m (x + L + 1) remAll'

def writeFn (inp : List Bool) : List Bool :=
  let n := (inp.takeWhile id).length
  let a := (inp.dropWhile id).tail
  let v := 2 * n
  let t := (v + 1).log2 + 1
  let L := 2 * (1 + v * t)
  let k := v * (L + 1)
  let w := k.bits.length
  (List.replicate k true ++ [false]) ++
    emitLeftBlocks w L n n 0 v a ++
    emitRightBlocks w L n (n * (L + 1)) n

abbrev WK := Fin 21
abbrev wIn      : WK := 0
abbrev wOut     : WK := 1
abbrev wOutRev  : WK := 2
abbrev wN       : WK := 3
abbrev wNloop   : WK := 4
abbrev wV       : WK := 5
abbrev wT       : WK := 6
abbrev wL       : WK := 7
abbrev wL1      : WK := 8
abbrev wLm1     : WK := 9
abbrev wX       : WK := 10
abbrev wY       : WK := 11
abbrev wRemLeft : WK := 12
abbrev wRemAll  : WK := 13
abbrev wRemR    : WK := 14
abbrev wRow     : WK := 15
abbrev wCnt     : WK := 16
abbrev wBlk     : WK := 17
abbrev wRxLoop  : WK := 18
abbrev wTmp1    : WK := 19
abbrev wTmp2    : WK := 20

def emitPairExec (S : WK → List Bool) : WK → List Bool :=
  revCopyExec wY wOutRev wTmp1 (revCopyExec wX wOutRev wTmp1 S)

def emitPairCost (S : WK → List Bool) : ℕ :=
  let S1 := revCopyExec wX wOutRev wTmp1 S
  (7 * (S1 wY).length + 3 * (S1 wTmp1).length + 2) +
    (7 * (S wX).length + 3 * (S wTmp1).length + 2)

theorem psb_emitPair : PureSB emitPairExec emitPairCost := by
  unfold emitPairExec emitPairCost
  exact psb_seq (psb_revCopy (a := wX) (b := wOutRev) (tmp := wTmp1) (by decide) (by decide) (by decide))
                (psb_revCopy (a := wY) (b := wOutRev) (tmp := wTmp1) (by decide) (by decide) (by decide))

theorem indep_emitPair {k : WK} (h1 : wX ≠ k) (h2 : wY ≠ k) (h3 : wOutRev ≠ k) (h4 : wTmp1 ≠ k) :
    Indep k emitPairExec := by
  unfold emitPairExec
  exact indep_seq (indep_revCopy h1 h3 h4) (indep_revCopy h2 h3 h4)

theorem emitPair_spec (S : WK → List Bool) (w x y : ℕ)
    (hX : S wX = fieldBits w x) (hY : S wY = fieldBits w y) (ht : S wTmp1 = []) :
    emitPairExec S = Function.update S wOutRev ((emitPairBits w x y).reverse ++ S wOutRev) ∧
    emitPairCost S ≤ 14 * w + 4 := by
  have h1 : revCopyExec wX wOutRev wTmp1 S =
      Function.update S wOutRev ((fieldBits w x).reverse ++ S wOutRev) := by
    rw [revCopyExec_of_empty (by decide) (by decide) (by decide) S ht, hX]
  have h2 : emitPairExec S =
      Function.update S wOutRev ((emitPairBits w x y).reverse ++ S wOutRev) := by
    simp only [emitPairExec, h1]
    rw [revCopyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, ht])]
    funext j
    by_cases j1 : j = wOutRev
    · subst j1
      simp only [Function.update_self, Function.update_of_ne (by decide : wY ≠ wOutRev), hY,
        emitPairBits, List.reverse_append, List.append_assoc]
    · simp [Fin.ext_iff, j1]
  refine ⟨h2, ?_⟩
  simp only [emitPairCost, h1, Function.update_of_ne (by decide : wY ≠ wOutRev),
    Function.update_of_ne (by decide : wTmp1 ≠ wOutRev), hX, hY, ht, fieldBits_length, List.length_nil]
  omega

def emitOneExec (S : WK → List Bool) : WK → List Bool :=
  incFixedExec wY wTmp1 (emitPairExec S)

def emitOneCost (S : WK → List Bool) : ℕ :=
  let S1 := emitPairExec S
  (5 * (S1 wY).length + 3 * (S1 wTmp1).length + 7) + emitPairCost S

theorem psb_emitOne : PureSB emitOneExec emitOneCost := by
  unfold emitOneExec emitOneCost
  exact psb_seq psb_emitPair (psb_incFixed (x := wY) (tmp := wTmp1) (by decide))

theorem indep_emitOne {k : WK} (h1 : wX ≠ k) (h2 : wY ≠ k) (h3 : wOutRev ≠ k) (h4 : wTmp1 ≠ k) :
    Indep k emitOneExec := by
  unfold emitOneExec
  exact indep_seq (indep_emitPair h1 h2 h3 h4) (indep_incFixed h2 h4)

theorem emitOne_spec (S : WK → List Bool) (w x y : ℕ)
    (hX : S wX = fieldBits w x) (hY : S wY = fieldBits w y) (ht : S wTmp1 = []) :
    emitOneExec S = Function.update (Function.update S wOutRev ((emitPairBits w x y).reverse ++ S wOutRev))
      wY (fieldBits w (y + 1)) ∧
    emitOneCost S ≤ 19 * w + 11 := by
  have hp := emitPair_spec S w x y hX hY ht
  refine ⟨?_, ?_⟩
  · simp only [emitOneExec, hp.1]
    rw [incFixedExec_of_empty (by decide) _ (by simp [Fin.ext_iff, ht]),
        Function.update_of_ne (by decide : wY ≠ wOutRev), hY, incFixedBits_fieldBits]
  · simp only [emitOneCost, hp.1, Function.update_of_ne (by decide : wY ≠ wOutRev),
      Function.update_of_ne (by decide : wTmp1 ≠ wOutRev), hY, ht, fieldBits_length, List.length_nil]
    have := hp.2; omega

def emitManyExec (S : WK → List Bool) : WK → List Bool :=
  (S wCnt).foldl (fun U _ => emitOneExec U) (Function.update S wCnt [])

def emitManyCost (S : WK → List Bool) : ℕ :=
  forEachCost wCnt (fun _ => emitOneExec) (fun _ => emitOneCost) (S wCnt) S

theorem psb_emitMany : PureSB emitManyExec emitManyCost :=
  psb_forEachIgn wCnt psb_emitOne
    (indep_emitOne (by decide) (by decide) (by decide) (by decide))

theorem indep_emitMany {k : WK} (h0 : wCnt ≠ k) (h1 : wX ≠ k) (h2 : wY ≠ k)
    (h3 : wOutRev ≠ k) (h4 : wTmp1 ≠ k) : Indep k emitManyExec := by
  intro S l
  simp only [emitManyExec]
  rw [Function.update_of_ne h0, Function.update_comm h0.symm]
  generalize S wCnt = lc; generalize Function.update S wCnt [] = U
  induction lc generalizing U with
  | nil => rfl
  | cons _ lc ih => simp only [List.foldl_cons]; rw [indep_emitOne h1 h2 h3 h4, ih]

theorem emitMany_spec (S : WK → List Bool) (w x y : ℕ)
    (hX : S wX = fieldBits w x) (hY : S wY = fieldBits w y) (ht : S wTmp1 = []) :
    emitManyExec S =
      Function.update (Function.update (Function.update S wCnt [])
        wOutRev ((emitRange w x y (S wCnt).length).reverse ++ S wOutRev))
        wY (fieldBits w (y + (S wCnt).length)) ∧
    emitManyCost S ≤ (S wCnt).length * (19 * w + 13) + 1 := by
  have hfold : ∀ (l : List Bool) (y0 : ℕ) (U : WK → List Bool),
      U wX = fieldBits w x → U wY = fieldBits w y0 → U wTmp1 = [] →
      l.foldl (fun W _ => emitOneExec W) U =
        Function.update (Function.update U wOutRev ((emitRange w x y0 l.length).reverse ++ U wOutRev))
          wY (fieldBits w (y0 + l.length)) ∧
      forEachCost wCnt (fun _ => emitOneExec) (fun _ => emitOneCost) l U ≤
        l.length * (19 * w + 13) + 1 := by
    intro l
    induction l with
    | nil =>
      intro y0 U _ hUY _
      refine ⟨?_, by simp [forEachCost]⟩
      funext j
      by_cases j1 : j = wY
      · subst j1; simp [Fin.ext_iff, hUY]
      by_cases j2 : j = wOutRev
      · subst j2; simp [Fin.ext_iff, emitRange_zero]
      simp [Fin.ext_iff, j1, j2]
    | cons _ l ih =>
      intro y0 U hUX hUY hUt
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have h1 := emitOne_spec U w x y0 hUX hUY hUt
      have h1' := emitOne_spec (Function.update U wCnt l) w x y0
        (by simp [Fin.ext_iff, hUX]) (by simp [Fin.ext_iff, hUY]) (by simp [Fin.ext_iff, hUt])
      have hr1 := ih (y0 + 1) (emitOneExec U)
        (by rw [h1.1]; simp [Fin.ext_iff, hUX]) (by rw [h1.1]; simp [Fin.ext_iff]) (by rw [h1.1]; simp [Fin.ext_iff, hUt])
      have hr2 := ih (y0 + 1) (emitOneExec (Function.update U wCnt l))
        (by rw [h1'.1]; simp [Fin.ext_iff, hUX]) (by rw [h1'.1]; simp [Fin.ext_iff]) (by rw [h1'.1]; simp [Fin.ext_iff, hUt])
      refine ⟨?_, ?_⟩
      · rw [hr1.1, h1.1, emitRange_succ_front, List.reverse_append]
        funext j
        by_cases j1 : j = wY
        · subst j1; simp [Fin.ext_iff, show y0 + 1 + l.length = y0 + (l.length + 1) by omega]
        by_cases j2 : j = wOutRev
        · subst j2; simp [Fin.ext_iff, List.append_assoc]
        simp [Fin.ext_iff, j1, j2]
      · have hc1 := h1'.2
        have hc2 := hr2.2
        have hmul : (l.length + 1) * (19 * w + 13) = l.length * (19 * w + 13) + (19 * w + 13) := by ring
        omega
  have hr1 := hfold (S wCnt) y (Function.update S wCnt [])
    (by simp [Fin.ext_iff, hX]) (by simp [Fin.ext_iff, hY]) (by simp [Fin.ext_iff, ht])
  have hr2 := hfold (S wCnt) y S hX hY ht
  refine ⟨?_, hr2.2⟩
  simp only [emitManyExec, hr1.1]
  funext j
  by_cases j1 : j = wY
  · subst j1; simp [Fin.ext_iff]
  by_cases j2 : j = wOutRev
  · subst j2; simp [Fin.ext_iff]
  by_cases j3 : j = wCnt
  · subst j3; simp [Fin.ext_iff]
  simp [Fin.ext_iff, j1, j2, j3]

def emitBlkStepExec (S : WK → List Bool) : WK → List Bool :=
  emitManyExec (copyExec wL1 wCnt wTmp1 S)

def emitBlkStepCost (S : WK → List Bool) : ℕ :=
  emitManyCost (copyExec wL1 wCnt wTmp1 S) + (7 * (S wL1).length + 4 * (S wTmp1).length + 2)

theorem psb_emitBlkStep : PureSB emitBlkStepExec emitBlkStepCost := by
  unfold emitBlkStepExec emitBlkStepCost
  exact psb_seq (psb_copy (a := wL1) (b := wCnt) (tmp := wTmp1) (by decide) (by decide) (by decide)) psb_emitMany

theorem indep_emitBlkStep {k : WK} (h0 : wL1 ≠ k) (h1 : wCnt ≠ k) (h2 : wX ≠ k)
    (h3 : wY ≠ k) (h4 : wOutRev ≠ k) (h5 : wTmp1 ≠ k) : Indep k emitBlkStepExec := by
  unfold emitBlkStepExec
  exact indep_seq (indep_copy h0 h1 h5) (indep_emitMany h1 h2 h3 h4 h5)

theorem emitBlkStep_spec (S : WK → List Bool) (w x y : ℕ)
    (hX : S wX = fieldBits w x) (hY : S wY = fieldBits w y) (hC : S wCnt = []) (ht : S wTmp1 = []) :
    emitBlkStepExec S =
      Function.update (Function.update S wOutRev ((emitRange w x y (S wL1).length).reverse ++ S wOutRev))
        wY (fieldBits w (y + (S wL1).length)) ∧
    emitBlkStepCost S ≤ (S wL1).length * (19 * w + 20) + 3 := by
  have hc : copyExec wL1 wCnt wTmp1 S = Function.update S wCnt (S wL1) := by
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S ht, hC, List.append_nil]
  have hm := emitMany_spec (copyExec wL1 wCnt wTmp1 S) w x y
    (by rw [hc]; simp [Fin.ext_iff, hX]) (by rw [hc]; simp [Fin.ext_iff, hY]) (by rw [hc]; simp [Fin.ext_iff, ht])
  refine ⟨?_, ?_⟩
  · simp only [emitBlkStepExec]
    rw [hm.1, hc]
    funext j
    by_cases j1 : j = wY
    · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = wOutRev
    · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = wCnt
    · subst j3; simp [Fin.ext_iff, hC]
    simp [Fin.ext_iff, j1, j2, j3]
  · simp only [emitBlkStepCost]
    have hm2 := hm.2
    have hlen : (copyExec wL1 wCnt wTmp1 S wCnt).length = (S wL1).length := by rw [hc]; simp
    rw [hlen] at hm2
    simp only [ht, List.length_nil] at hm2 ⊢
    have hmul : (S wL1).length * (19 * w + 20) = (S wL1).length * (19 * w + 13) + 7 * (S wL1).length := by ring
    omega

def emitBlocksExec (S : WK → List Bool) : WK → List Bool :=
  (S wBlk).foldl (fun U _ => emitBlkStepExec U) (Function.update S wBlk [])

def emitBlocksCost (S : WK → List Bool) : ℕ :=
  forEachCost wBlk (fun _ => emitBlkStepExec) (fun _ => emitBlkStepCost) (S wBlk) S

theorem psb_emitBlocks : PureSB emitBlocksExec emitBlocksCost :=
  psb_forEachIgn wBlk psb_emitBlkStep
    (indep_emitBlkStep (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))

theorem indep_emitBlocks {k : WK} (hb : wBlk ≠ k) (h0 : wL1 ≠ k) (h1 : wCnt ≠ k)
    (h2 : wX ≠ k) (h3 : wY ≠ k) (h4 : wOutRev ≠ k) (h5 : wTmp1 ≠ k) :
    Indep k emitBlocksExec := by
  intro S l
  simp only [emitBlocksExec]
  rw [Function.update_of_ne hb, Function.update_comm hb.symm]
  generalize S wBlk = lb; generalize Function.update S wBlk [] = U
  induction lb generalizing U with
  | nil => rfl
  | cons _ lb ih => simp only [List.foldl_cons]; rw [indep_emitBlkStep h0 h1 h2 h3 h4 h5, ih]

theorem emitBlocks_spec (S : WK → List Bool) (w x y : ℕ)
    (hX : S wX = fieldBits w x) (hY : S wY = fieldBits w y) (hC : S wCnt = []) (ht : S wTmp1 = []) :
    emitBlocksExec S =
      Function.update (Function.update (Function.update S wBlk [])
        wOutRev ((emitRange w x y ((S wBlk).length * (S wL1).length)).reverse ++ S wOutRev))
        wY (fieldBits w (y + (S wBlk).length * (S wL1).length)) ∧
    emitBlocksCost S ≤ (S wBlk).length * ((S wL1).length * (19 * w + 20) + 5) + 1 := by
  have hfold : ∀ (l : List Bool) (y0 : ℕ) (U : WK → List Bool),
      U wX = fieldBits w x → U wY = fieldBits w y0 → U wCnt = [] → U wTmp1 = [] →
      l.foldl (fun W _ => emitBlkStepExec W) U =
        Function.update (Function.update U wOutRev ((emitRange w x y0 (l.length * (U wL1).length)).reverse ++ U wOutRev))
          wY (fieldBits w (y0 + l.length * (U wL1).length)) ∧
      forEachCost wBlk (fun _ => emitBlkStepExec) (fun _ => emitBlkStepCost) l U ≤
        l.length * ((U wL1).length * (19 * w + 20) + 5) + 1 := by
    intro l
    induction l with
    | nil =>
      intro y0 U _ hUY _ _
      refine ⟨?_, by simp [forEachCost]⟩
      funext j
      by_cases j1 : j = wY
      · subst j1; simp [Fin.ext_iff, hUY]
      by_cases j2 : j = wOutRev
      · subst j2; simp [Fin.ext_iff, emitRange_zero]
      simp [Fin.ext_iff, j1, j2]
    | cons _ l ih =>
      intro y0 U hUX hUY hUC hUt
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have h1 := emitBlkStep_spec U w x y0 hUX hUY hUC hUt
      have h1' := emitBlkStep_spec (Function.update U wBlk l) w x y0
        (by simp [Fin.ext_iff, hUX]) (by simp [Fin.ext_iff, hUY]) (by simp [Fin.ext_iff, hUC]) (by simp [Fin.ext_iff, hUt])
      have hr1 := ih (y0 + (U wL1).length) (emitBlkStepExec U)
        (by rw [h1.1]; simp [Fin.ext_iff, hUX]) (by rw [h1.1]; simp [Fin.ext_iff]) (by rw [h1.1]; simp [Fin.ext_iff, hUC]) (by rw [h1.1]; simp [Fin.ext_iff, hUt])
      have hr2 := ih (y0 + (U wL1).length) (emitBlkStepExec (Function.update U wBlk l))
        (by rw [h1'.1]; simp [Fin.ext_iff, hUX]) (by rw [h1'.1]; simp [Fin.ext_iff]) (by rw [h1'.1]; simp [Fin.ext_iff, hUC]) (by rw [h1'.1]; simp [Fin.ext_iff, hUt])
      have hL1eq : (emitBlkStepExec U wL1).length = (U wL1).length := by rw [h1.1]; simp [Fin.ext_iff]
      have hL1eq' : (emitBlkStepExec (Function.update U wBlk l) wL1).length = (U wL1).length := by
        rw [h1'.1]; simp [Fin.ext_iff]
      refine ⟨?_, ?_⟩
      · rw [hr1.1, hL1eq, h1.1]
        have hmul : (l.length + 1) * (U wL1).length = (U wL1).length + l.length * (U wL1).length := by ring
        rw [hmul, emitRange_add, List.reverse_append]
        funext j
        by_cases j1 : j = wY
        · subst j1; simp [Fin.ext_iff, Nat.add_assoc]
        by_cases j2 : j = wOutRev
        · subst j2; simp [Fin.ext_iff, List.append_assoc]
        simp [Fin.ext_iff, j1, j2]
      · have hc1 := h1'.2
        simp only [Function.update_of_ne (by decide : wL1 ≠ wBlk)] at hc1
        have hc2 := hr2.2
        rw [hL1eq'] at hc2
        have hmul : (l.length + 1) * ((U wL1).length * (19 * w + 20) + 5) =
            l.length * ((U wL1).length * (19 * w + 20) + 5) + ((U wL1).length * (19 * w + 20) + 5) := by ring
        omega
  have hr1 := hfold (S wBlk) y (Function.update S wBlk [])
    (by simp [Fin.ext_iff, hX]) (by simp [Fin.ext_iff, hY]) (by simp [Fin.ext_iff, hC]) (by simp [Fin.ext_iff, ht])
  have hr2 := hfold (S wBlk) y S hX hY hC ht
  refine ⟨?_, hr2.2⟩
  simp only [emitBlocksExec, hr1.1]
  funext j
  by_cases j1 : j = wY
  · subst j1; simp [Fin.ext_iff]
  by_cases j2 : j = wOutRev
  · subst j2; simp [Fin.ext_iff]
  by_cases j3 : j = wBlk
  · subst j3; simp [Fin.ext_iff]
  simp [Fin.ext_iff, j1, j2, j3]

def sameBlkEmitExec (S : WK → List Bool) : WK → List Bool :=
  match S wCnt with
  | [] => Function.update S wCnt []
  | false :: l => emitManyExec (incFixedExec wY wTmp1 (Function.update S wCnt l))
  | true :: l => emitManyExec (incFixedExec wY wTmp1 (Function.update S wCnt l))

def sameBlkEmitCost (S : WK → List Bool) : ℕ :=
  match S wCnt with
  | [] => 3
  | false :: l =>
    let U := Function.update S wCnt l
    (emitManyCost (incFixedExec wY wTmp1 U) + (5 * (U wY).length + 3 * (U wTmp1).length + 7)) + 3
  | true :: l =>
    let U := Function.update S wCnt l
    (emitManyCost (incFixedExec wY wTmp1 U) + (5 * (U wY).length + 3 * (U wTmp1).length + 7)) + 3

theorem psb_sameBlkEmit : PureSB sameBlkEmitExec sameBlkEmitCost := by
  unfold sameBlkEmitExec sameBlkEmitCost
  exact psb_branchPop wCnt psb_noop (psb_seq (psb_incFixed (x := wY) (tmp := wTmp1) (by decide)) psb_emitMany)
    (psb_seq (psb_incFixed (x := wY) (tmp := wTmp1) (by decide)) psb_emitMany)

theorem indep_sameBlkEmit {k : WK} (h0 : wCnt ≠ k) (h1 : wX ≠ k) (h2 : wY ≠ k)
    (h3 : wOutRev ≠ k) (h4 : wTmp1 ≠ k) : Indep k sameBlkEmitExec := by
  intro S l
  simp only [sameBlkEmitExec, Function.update_of_ne h0]
  cases S wCnt with
  | nil => dsimp only; rw [Function.update_comm h0.symm]
  | cons b lc =>
    cases b <;> (dsimp only; rw [Function.update_comm h0.symm, indep_incFixed h2 h4, indep_emitMany h0 h1 h2 h3 h4])

def noBaseRxExec (S : WK → List Bool) : WK → List Bool :=
  let S1 := Function.update S wRemR (S wRemR).tail
  let S2 := copyExec wX wY wTmp1 S1
  let S3 := incFixedExec wY wTmp1 S2
  let S4 := copyExec wRemR wCnt wTmp1 S3
  let S5 := sameBlkEmitExec S4
  let S6 := copyExec wRemAll wBlk wTmp1 S5
  let S7 := emitBlocksExec S6
  let S8 := clearExec wY S7
  incFixedExec wX wTmp1 S8

def noBaseRxCost (S : WK → List Bool) : ℕ :=
  let S1 := Function.update S wRemR (S wRemR).tail
  let S2 := copyExec wX wY wTmp1 S1
  let S3 := incFixedExec wY wTmp1 S2
  let S4 := copyExec wRemR wCnt wTmp1 S3
  let S5 := sameBlkEmitExec S4
  let S6 := copyExec wRemAll wBlk wTmp1 S5
  let S7 := emitBlocksExec S6
  let S8 := clearExec wY S7
  (5 * (S8 wX).length + 3 * (S8 wTmp1).length + 7) +
    ((3 * (S7 wY).length + 1) +
      (emitBlocksCost S6 +
        ((7 * (S5 wRemAll).length + 4 * (S5 wTmp1).length + 2) +
          (sameBlkEmitCost S4 +
            ((7 * (S3 wRemR).length + 4 * (S3 wTmp1).length + 2) +
              ((5 * (S2 wY).length + 3 * (S2 wTmp1).length + 7) +
                ((7 * (S1 wX).length + 4 * (S1 wTmp1).length + 2) + 1)))))))

theorem psb_noBaseRx : PureSB noBaseRxExec noBaseRxCost := by
  have h1 := psb_popDrop wRemR
  have h2 := psb_seq h1 (psb_copy (a := wX) (b := wY) (tmp := wTmp1) (by decide) (by decide) (by decide))
  have h3 := psb_seq h2 (psb_incFixed (x := wY) (tmp := wTmp1) (by decide))
  have h4 := psb_seq h3 (psb_copy (a := wRemR) (b := wCnt) (tmp := wTmp1) (by decide) (by decide) (by decide))
  have h5 := psb_seq h4 psb_sameBlkEmit
  have h6 := psb_seq h5 (psb_copy (a := wRemAll) (b := wBlk) (tmp := wTmp1) (by decide) (by decide) (by decide))
  have h7 := psb_seq h6 psb_emitBlocks
  have h8 := psb_seq h7 (psb_clear wY)
  have h9 := psb_seq h8 (psb_incFixed (x := wX) (tmp := wTmp1) (by decide))
  exact h9

theorem indep_noBaseRx {k : WK} (hr : wRemR ≠ k) (hx : wX ≠ k) (hy : wY ≠ k) (ht : wTmp1 ≠ k)
    (hc : wCnt ≠ k) (ho : wOutRev ≠ k) (ha : wRemAll ≠ k) (hb : wBlk ≠ k) (hl : wL1 ≠ k) :
    Indep k noBaseRxExec := by
  have h1 := indep_popDrop hr
  have h2 := indep_seq h1 (indep_copy hx hy ht)
  have h3 := indep_seq h2 (indep_incFixed hy ht)
  have h4 := indep_seq h3 (indep_copy hr hc ht)
  have h5 := indep_seq h4 (indep_sameBlkEmit hc hx hy ho ht)
  have h6 := indep_seq h5 (indep_copy ha hb ht)
  have h7 := indep_seq h6 (indep_emitBlocks hb hl hc hx hy ho ht)
  have h8 := indep_seq h7 (indep_clear hy)
  have h9 := indep_seq h8 (indep_incFixed hx ht)
  exact h9

theorem noBaseRx_spec (S : WK → List Bool) (w x r : ℕ) (hRemR : (S wRemR).length = r + 1)
    (hX : S wX = fieldBits w x) (hY : S wY = []) (hC : S wCnt = []) (hB : S wBlk = [])
    (ht : S wTmp1 = []) :
    noBaseRxExec S =
      Function.update (Function.update (Function.update S wRemR (S wRemR).tail)
        wOutRev ((emitNoBase w x r (S wRemAll).length (S wL1).length).reverse ++ S wOutRev))
        wX (fieldBits w (x + 1)) ∧
    noBaseRxCost S ≤
      (r + (S wRemAll).length * (S wL1).length) * (19 * w + 20) +
        12 * (S wRemAll).length + 7 * r + 25 * w + 35 := by
  have htail_len : (S wRemR).tail.length = r := by rw [List.length_tail, hRemR]; omega
  let S1 := Function.update S wRemR (S wRemR).tail
  have hS2 : copyExec wX wY wTmp1 S1 = Function.update S1 wY (fieldBits w x) := by
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S1 (by simp [Fin.ext_iff, S1, ht])]
    simp [Fin.ext_iff, S1, hX, hY]
  have hS3 : incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1) = Function.update S1 wY (fieldBits w (x + 1)) := by
    rw [hS2, incFixedExec_of_empty (by decide) _ (by simp [Fin.ext_iff, S1, ht]), Function.update_self,
        incFixedBits_fieldBits, Function.update_idem]
  have hS4 : copyExec wRemR wCnt wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1)) =
      Function.update (Function.update S1 wY (fieldBits w (x + 1))) wCnt (S wRemR).tail := by
    rw [hS3, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, S1, ht])]
    simp [Fin.ext_iff, S1, hC]
  have hS5_both :
      sameBlkEmitExec (Function.update (Function.update S1 wY (fieldBits w (x + 1))) wCnt (S wRemR).tail) =
        Function.update (Function.update S1 wOutRev
          ((if r = 0 then [] else emitRange w x (x + 2) (r - 1)).reverse ++ S wOutRev))
          wY (fieldBits w (x + 1 + r)) ∧
      sameBlkEmitCost (Function.update (Function.update S1 wY (fieldBits w (x + 1))) wCnt (S wRemR).tail) ≤
        r * (19 * w + 13) + 5 * w + 11 := by
    cases htl : (S wRemR).tail with
    | nil =>
      have hr0 : r = 0 := by rw [htl] at htail_len; simpa using htail_len.symm
      subst hr0
      refine ⟨?_, by simp [sameBlkEmitCost]⟩
      simp only [sameBlkEmitExec, Function.update_self, ↓reduceIte, List.reverse_nil, List.nil_append]
      funext j
      by_cases j1 : j = wY
      · subst j1; simp [Fin.ext_iff]
      by_cases j2 : j = wOutRev
      · subst j2; simp [Fin.ext_iff, S1]
      by_cases j3 : j = wCnt
      · subst j3; simp [Fin.ext_iff, S1, hC]
      simp [Fin.ext_iff, j1, j2, j3]
    | cons b lr =>
      have hrpos : r = lr.length + 1 := by rw [htl] at htail_len; simpa using htail_len.symm
      have hrne : r ≠ 0 := by omega
      have hincY : incFixedExec wY wTmp1 (Function.update (Function.update (Function.update S1
          wY (fieldBits w (x + 1))) wCnt (b :: lr)) wCnt lr) =
          Function.update (Function.update S1 wCnt lr) wY (fieldBits w (x + 2)) := by
        rw [incFixedExec_of_empty (by decide) _ (by simp [Fin.ext_iff, S1, ht])]
        simp only [Function.update_of_ne (by decide : wY ≠ wCnt), Function.update_self,
          incFixedBits_fieldBits, show x + 1 + 1 = x + 2 by omega]
        funext j
        by_cases j1 : j = wY
        · subst j1; simp [Fin.ext_iff]
        by_cases j2 : j = wCnt
        · subst j2; simp [Fin.ext_iff]
        simp [Fin.ext_iff, j1, j2]
      have hm := emitMany_spec (Function.update (Function.update S1 wCnt lr) wY (fieldBits w (x + 2)))
        w x (x + 2) (by simp [Fin.ext_iff, S1, hX]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff, S1, ht])
      have hlrlen : (Function.update (Function.update S1 wCnt lr) wY (fieldBits w (x + 2)) wCnt).length = r - 1 := by
        simp [Fin.ext_iff]; omega
      have hmain : emitManyExec (incFixedExec wY wTmp1 (Function.update (Function.update (Function.update S1
          wY (fieldBits w (x + 1))) wCnt (b :: lr)) wCnt lr)) =
          Function.update (Function.update S1 wOutRev ((emitRange w x (x + 2) (r - 1)).reverse ++ S wOutRev))
            wY (fieldBits w (x + 1 + r)) := by
        rw [hincY, hm.1, hlrlen, show x + 2 + (r - 1) = x + 1 + r by omega]
        funext j
        by_cases j1 : j = wY
        · subst j1; simp [Fin.ext_iff]
        by_cases j2 : j = wOutRev
        · subst j2; simp [Fin.ext_iff, S1]
        by_cases j3 : j = wCnt
        · subst j3; simp [Fin.ext_iff, S1, hC]
        simp [Fin.ext_iff, j1, j2, j3]
      have hcost : (emitManyCost (incFixedExec wY wTmp1 (Function.update (Function.update (Function.update S1
          wY (fieldBits w (x + 1))) wCnt (b :: lr)) wCnt lr)) +
          (5 * (Function.update (Function.update (Function.update S1 wY (fieldBits w (x + 1))) wCnt (b :: lr)) wCnt lr wY).length +
           3 * (Function.update (Function.update (Function.update S1 wY (fieldBits w (x + 1))) wCnt (b :: lr)) wCnt lr wTmp1).length + 7)) + 3 ≤
          r * (19 * w + 13) + 5 * w + 11 := by
        rw [hincY]
        have hm2 := hm.2; rw [hlrlen] at hm2
        simp only [Function.update_of_ne (by decide : wY ≠ wCnt), Function.update_self,
          Function.update_of_ne (by decide : wTmp1 ≠ wCnt), Function.update_of_ne (by decide : wTmp1 ≠ wY),
          S1, Function.update_of_ne (by decide : wTmp1 ≠ wRemR), fieldBits_length, ht, List.length_nil] at hm2 ⊢
        have hle : (r - 1) * (19 * w + 13) ≤ r * (19 * w + 13) := Nat.mul_le_mul_right _ (Nat.sub_le r 1)
        omega
      cases b
      · exact ⟨by simpa [sameBlkEmitExec, hrne] using hmain, by simpa [sameBlkEmitCost] using hcost⟩
      · exact ⟨by simpa [sameBlkEmitExec, hrne] using hmain, by simpa [sameBlkEmitCost] using hcost⟩
  have hS5 := hS5_both.1
  have hS6 : copyExec wRemAll wBlk wTmp1
      (sameBlkEmitExec (Function.update (Function.update S1 wY (fieldBits w (x + 1))) wCnt (S wRemR).tail)) =
      Function.update (Function.update (Function.update S1 wOutRev
        ((if r = 0 then [] else emitRange w x (x + 2) (r - 1)).reverse ++ S wOutRev))
        wY (fieldBits w (x + 1 + r))) wBlk (S wRemAll) := by
    rw [hS5, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, S1, ht])]
    simp [Fin.ext_iff, S1, hB]
  have hBlks := emitBlocks_spec
    (Function.update (Function.update (Function.update S1 wOutRev
      ((if r = 0 then [] else emitRange w x (x + 2) (r - 1)).reverse ++ S wOutRev))
      wY (fieldBits w (x + 1 + r))) wBlk (S wRemAll))
    w x (x + 1 + r) (by simp [Fin.ext_iff, S1, hX]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff, S1, hC]) (by simp [Fin.ext_iff, S1, ht])
  have hS7 : emitBlocksExec (copyExec wRemAll wBlk wTmp1
      (sameBlkEmitExec (Function.update (Function.update S1 wY (fieldBits w (x + 1))) wCnt (S wRemR).tail))) =
      Function.update (Function.update S1 wOutRev
        ((emitNoBase w x r (S wRemAll).length (S wL1).length).reverse ++ S wOutRev))
        wY (fieldBits w (x + 1 + r + (S wRemAll).length * (S wL1).length)) := by
    rw [hS6, hBlks.1]
    funext j
    by_cases j1 : j = wY
    · subst j1; simp [Fin.ext_iff, S1]
    by_cases j2 : j = wOutRev
    · subst j2; simp [Fin.ext_iff, S1, emitNoBase, List.reverse_append, List.append_assoc]
    by_cases j3 : j = wBlk
    · subst j3; simp [Fin.ext_iff, S1, hB]
    simp [Fin.ext_iff, j1, j2, j3]
  refine ⟨?_, ?_⟩
  · simp only [noBaseRxExec]
    change incFixedExec wX wTmp1 (clearExec wY (emitBlocksExec (copyExec wRemAll wBlk wTmp1
      (sameBlkEmitExec (copyExec wRemR wCnt wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1))))))) = _
    rw [hS4, hS7]
    rw [incFixedExec_of_empty (by decide) _ (by simp [Fin.ext_iff, clearExec, S1, ht])]
    funext j
    by_cases j1 : j = wX
    · subst j1; simp [Fin.ext_iff, clearExec, S1, hX, incFixedBits_fieldBits]
    by_cases j2 : j = wOutRev
    · subst j2; simp [Fin.ext_iff, clearExec]
    by_cases j3 : j = wY
    · subst j3; simp [Fin.ext_iff, clearExec, S1, hY]
    by_cases j4 : j = wRemR
    · subst j4; simp [Fin.ext_iff, clearExec, S1]
    simp [Fin.ext_iff, clearExec, S1, j1, j2, j3, j4]
  · simp only [noBaseRxCost]
    change (5 * (clearExec wY (emitBlocksExec (copyExec wRemAll wBlk wTmp1
        (sameBlkEmitExec (copyExec wRemR wCnt wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1)))))) wX).length +
      3 * (clearExec wY (emitBlocksExec (copyExec wRemAll wBlk wTmp1
        (sameBlkEmitExec (copyExec wRemR wCnt wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1)))))) wTmp1).length + 7) +
      ((3 * (emitBlocksExec (copyExec wRemAll wBlk wTmp1
          (sameBlkEmitExec (copyExec wRemR wCnt wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1))))) wY).length + 1) +
        (emitBlocksCost (copyExec wRemAll wBlk wTmp1
            (sameBlkEmitExec (copyExec wRemR wCnt wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1))))) +
          ((7 * (sameBlkEmitExec (copyExec wRemR wCnt wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1))) wRemAll).length +
            4 * (sameBlkEmitExec (copyExec wRemR wCnt wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1))) wTmp1).length + 2) +
            (sameBlkEmitCost (copyExec wRemR wCnt wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1))) +
              ((7 * (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1) wRemR).length +
                4 * (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S1) wTmp1).length + 2) +
                ((5 * (copyExec wX wY wTmp1 S1 wY).length + 3 * (copyExec wX wY wTmp1 S1 wTmp1).length + 7) +
                  ((7 * (S1 wX).length + 4 * (S1 wTmp1).length + 2) + 1))))))) ≤ _
    rw [hS4, hS7, hS6, hS5, hS3, hS2]
    have hbc := hBlks.2
    have hsc := hS5_both.2
    simp only [clearExec, S1, Function.update_self, Function.update_of_ne (by decide : wX ≠ wY),
      Function.update_of_ne (by decide : wX ≠ wOutRev), Function.update_of_ne (by decide : wX ≠ wRemR),
      Function.update_of_ne (by decide : wTmp1 ≠ wY), Function.update_of_ne (by decide : wTmp1 ≠ wOutRev),
      Function.update_of_ne (by decide : wTmp1 ≠ wRemR), Function.update_of_ne (by decide : wRemAll ≠ wY),
      Function.update_of_ne (by decide : wRemAll ≠ wOutRev), Function.update_of_ne (by decide : wRemAll ≠ wRemR),
      Function.update_of_ne (by decide : wRemR ≠ wY), Function.update_of_ne (by decide : wL1 ≠ wBlk),
      Function.update_of_ne (by decide : wL1 ≠ wY), Function.update_of_ne (by decide : wL1 ≠ wOutRev),
      Function.update_of_ne (by decide : wL1 ≠ wRemR), hX, ht, htail_len, fieldBits_length,
      List.length_nil] at hbc hsc ⊢
    have hmul : (r + (S wRemAll).length * (S wL1).length) * (19 * w + 20) =
        r * (19 * w + 20) + (S wRemAll).length * (S wL1).length * (19 * w + 20) := by ring
    have hmul2 : (S wRemAll).length * ((S wL1).length * (19 * w + 20) + 5) =
        (S wRemAll).length * (S wL1).length * (19 * w + 20) + 5 * (S wRemAll).length := by ring
    have hmul3 : r * (19 * w + 13) ≤ r * (19 * w + 20) := Nat.mul_le_mul_left r (by omega)
    omega


def noBaseLoopExec (S : WK → List Bool) : WK → List Bool :=
  (S wRxLoop).foldl (fun U _ => noBaseRxExec U) (Function.update S wRxLoop [])

def noBaseLoopCost (S : WK → List Bool) : ℕ :=
  forEachCost wRxLoop (fun _ => noBaseRxExec) (fun _ => noBaseRxCost) (S wRxLoop) S

theorem psb_noBaseLoop : PureSB noBaseLoopExec noBaseLoopCost :=
  psb_forEachIgn wRxLoop psb_noBaseRx
    (indep_noBaseRx (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide))

theorem indep_noBaseLoop {k : WK} (hlp : wRxLoop ≠ k) (hr : wRemR ≠ k) (hx : wX ≠ k)
    (hy : wY ≠ k) (ht : wTmp1 ≠ k) (hc : wCnt ≠ k) (ho : wOutRev ≠ k)
    (ha : wRemAll ≠ k) (hb : wBlk ≠ k) (hl : wL1 ≠ k) :
    Indep k noBaseLoopExec := by
  intro S l
  simp only [noBaseLoopExec]
  rw [Function.update_of_ne hlp, Function.update_comm hlp.symm]
  generalize S wRxLoop = lp; generalize Function.update S wRxLoop [] = U
  induction lp generalizing U with
  | nil => rfl
  | cons _ lp ih =>
    simp only [List.foldl_cons]
    rw [indep_noBaseRx hr hx hy ht hc ho ha hb hl, ih]

theorem noBaseLoop_spec (S : WK → List Bool) (w x : ℕ)
    (hLen : (S wRemR).length = (S wRxLoop).length)
    (hX : S wX = fieldBits w x) (hY : S wY = []) (hC : S wCnt = []) (hB : S wBlk = [])
    (ht : S wTmp1 = []) :
    noBaseLoopExec S =
      Function.update (Function.update (Function.update (Function.update S wRxLoop []) wRemR [])
        wOutRev ((emitNoBaseLoop w x (S wRemAll).length (S wL1).length (S wRxLoop).length).reverse ++ S wOutRev))
        wX (fieldBits w (x + (S wRxLoop).length)) ∧
    noBaseLoopCost S ≤
      (S wRxLoop).length *
        (((S wRxLoop).length + (S wRemAll).length * (S wL1).length) * (19 * w + 20) +
          12 * (S wRemAll).length + 7 * (S wRxLoop).length + 25 * w + 37) + 1 := by
  have hfold : ∀ (l : List Bool) (x0 : ℕ) (U : WK → List Bool),
      (U wRemR).length = l.length → U wX = fieldBits w x0 →
      U wY = [] → U wCnt = [] → U wBlk = [] → U wTmp1 = [] →
      l.foldl (fun W _ => noBaseRxExec W) U =
        Function.update (Function.update (Function.update U wRemR [])
          wOutRev ((emitNoBaseLoop w x0 (U wRemAll).length (U wL1).length l.length).reverse ++ U wOutRev))
          wX (fieldBits w (x0 + l.length)) ∧
      forEachCost wRxLoop (fun _ => noBaseRxExec) (fun _ => noBaseRxCost) l U ≤
        l.length *
          ((l.length + (U wRemAll).length * (U wL1).length) * (19 * w + 20) +
            12 * (U wRemAll).length + 7 * l.length + 25 * w + 37) + 1 := by
    intro l
    induction l with
    | nil =>
      intro x0 U hlen hUX _ _ _ _
      have hR0 : U wRemR = [] := List.eq_nil_of_length_eq_zero hlen
      refine ⟨?_, by simp [forEachCost]⟩
      funext j
      by_cases j1 : j = wX; · subst j1; simp [Fin.ext_iff, hUX]
      by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff, emitNoBaseLoop]
      by_cases j3 : j = wRemR; · subst j3; simp [Fin.ext_iff, hR0]
      simp [Fin.ext_iff, j1, j2, j3]
    | cons _ l ih =>
      intro x0 U hlen hUX hUY hUC hUB hUt
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have h1 := noBaseRx_spec U w x0 l.length hlen hUX hUY hUC hUB hUt
      have h1' := noBaseRx_spec (Function.update U wRxLoop l) w x0 l.length
        (by simp [Fin.ext_iff, hlen]) (by simp [Fin.ext_iff, hUX]) (by simp [Fin.ext_iff, hUY])
        (by simp [Fin.ext_iff, hUC]) (by simp [Fin.ext_iff, hUB]) (by simp [Fin.ext_iff, hUt])
      have htl : (U wRemR).tail.length = l.length := by simp only [List.length_tail, hlen, List.length_cons]; omega
      have hr1 := ih (x0 + 1) (noBaseRxExec U) (by rw [h1.1]; simp [Fin.ext_iff, htl])
        (by rw [h1.1]; simp [Fin.ext_iff]) (by rw [h1.1]; simp [Fin.ext_iff, hUY])
        (by rw [h1.1]; simp [Fin.ext_iff, hUC]) (by rw [h1.1]; simp [Fin.ext_iff, hUB])
        (by rw [h1.1]; simp [Fin.ext_iff, hUt])
      have hr2 := ih (x0 + 1) (noBaseRxExec (Function.update U wRxLoop l))
        (by rw [h1'.1]; simp [Fin.ext_iff, htl]) (by rw [h1'.1]; simp [Fin.ext_iff])
        (by rw [h1'.1]; simp [Fin.ext_iff, hUY]) (by rw [h1'.1]; simp [Fin.ext_iff, hUC])
        (by rw [h1'.1]; simp [Fin.ext_iff, hUB]) (by rw [h1'.1]; simp [Fin.ext_iff, hUt])
      have hA1 : (noBaseRxExec U wRemAll).length = (U wRemAll).length := by rw [h1.1]; simp [Fin.ext_iff]
      have hL1' : (noBaseRxExec U wL1).length = (U wL1).length := by rw [h1.1]; simp [Fin.ext_iff]
      have hA2 : (noBaseRxExec (Function.update U wRxLoop l) wRemAll).length = (U wRemAll).length := by
        rw [h1'.1]; simp [Fin.ext_iff]
      have hL2' : (noBaseRxExec (Function.update U wRxLoop l) wL1).length = (U wL1).length := by
        rw [h1'.1]; simp [Fin.ext_iff]
      refine ⟨?_, ?_⟩
      · rw [hr1.1, hA1, hL1', h1.1]
        funext j
        by_cases j1 : j = wX
        · subst j1; simp [Fin.ext_iff, show x0 + 1 + l.length = x0 + (l.length + 1) by omega]
        by_cases j2 : j = wOutRev
        · subst j2; simp [Fin.ext_iff, emitNoBaseLoop, List.reverse_append, List.append_assoc]
        by_cases j3 : j = wRemR
        · subst j3; simp [Fin.ext_iff]
        simp [Fin.ext_iff, j1, j2, j3]
      · have hc1 := h1'.2
        simp only [Function.update_of_ne (by decide : wRemAll ≠ wRxLoop),
          Function.update_of_ne (by decide : wL1 ≠ wRxLoop)] at hc1
        have hc2 := hr2.2
        rw [hA2, hL2'] at hc2
        set M := (l.length + 1 + (U wRemAll).length * (U wL1).length) * (19 * w + 20) +
            12 * (U wRemAll).length + 7 * (l.length + 1) + 25 * w + 37
        have hM1 : noBaseRxCost (Function.update U wRxLoop l) + 2 ≤ M := by
          have hle : (l.length + (U wRemAll).length * (U wL1).length) * (19 * w + 20) ≤
              (l.length + 1 + (U wRemAll).length * (U wL1).length) * (19 * w + 20) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have hM2 : l.length * ((l.length + (U wRemAll).length * (U wL1).length) * (19 * w + 20) +
            12 * (U wRemAll).length + 7 * l.length + 25 * w + 37) ≤ l.length * M := by
          refine Nat.mul_le_mul_left _ ?_
          have hle : (l.length + (U wRemAll).length * (U wL1).length) * (19 * w + 20) ≤
              (l.length + 1 + (U wRemAll).length * (U wL1).length) * (19 * w + 20) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        have hmul : (l.length + 1) * M = l.length * M + M := by ring
        omega
  have hr1 := hfold (S wRxLoop) x (Function.update S wRxLoop []) (by simp [Fin.ext_iff, hLen])
    (by simp [Fin.ext_iff, hX]) (by simp [Fin.ext_iff, hY]) (by simp [Fin.ext_iff, hC])
    (by simp [Fin.ext_iff, hB]) (by simp [Fin.ext_iff, ht])
  have hr2 := hfold (S wRxLoop) x S hLen hX hY hC hB ht
  refine ⟨?_, hr2.2⟩
  simp only [noBaseLoopExec, hr1.1]
  funext j
  by_cases j1 : j = wX; · subst j1; simp [Fin.ext_iff]
  by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff]
  by_cases j3 : j = wRemR; · subst j3; simp [Fin.ext_iff]
  by_cases j4 : j = wRxLoop; · subst j4; simp [Fin.ext_iff]
  simp [Fin.ext_iff, j1, j2, j3, j4]

def readOneBitExec (S : WK → List Bool) : WK → List Bool :=
  match S wIn with
  | [] => Function.update (Function.update S wIn []) wTmp2 (false :: (Function.update S wIn []) wTmp2)
  | false :: l => Function.update (Function.update S wIn l) wTmp2 (false :: (Function.update S wIn l) wTmp2)
  | true :: l => Function.update (Function.update S wIn l) wTmp2 (true :: (Function.update S wIn l) wTmp2)

theorem psb_readOneBit : PureSB readOneBitExec (fun _ => 4) := by
  unfold readOneBitExec
  refine psb_mono (psb_branchPop wIn (psb_push wTmp2 false) (psb_push wTmp2 false) (psb_push wTmp2 true)) ?_
  intro S; cases S wIn with | nil => simp | cons b _ => cases b <;> simp

theorem indep_readOneBit {k : WK} (h1 : wIn ≠ k) (h2 : wTmp2 ≠ k) : Indep k readOneBitExec := by
  intro S l
  simp only [readOneBitExec, Function.update_of_ne h1]
  cases S wIn with
  | nil =>
    funext j
    by_cases j1 : j = k; · subst j1; simp [h1.symm, h2.symm]
    by_cases j2 : j = wTmp2; · subst j2; simp [Fin.ext_iff, h2]
    by_cases j3 : j = wIn; · subst j3; simp [Fin.ext_iff, h1]
    simp [j1, j2, j3]
  | cons b lr =>
    cases b
    · funext j
      by_cases j1 : j = k; · subst j1; simp [h1.symm, h2.symm]
      by_cases j2 : j = wTmp2; · subst j2; simp [Fin.ext_iff, h2]
      by_cases j3 : j = wIn; · subst j3; simp [Fin.ext_iff, h1]
      simp [j1, j2, j3]
    · funext j
      by_cases j1 : j = k; · subst j1; simp [h1.symm, h2.symm]
      by_cases j2 : j = wTmp2; · subst j2; simp [Fin.ext_iff, h2]
      by_cases j3 : j = wIn; · subst j3; simp [Fin.ext_iff, h1]
      simp [j1, j2, j3]

def readRowExec (S : WK → List Bool) : WK → List Bool :=
  let S1 := copyExec wN wCnt wTmp1 S
  let S2 := (S1 wCnt).foldl (fun U _ => readOneBitExec U) (Function.update S1 wCnt [])
  revMoveExec wTmp2 wRow S2

def readRowCost (S : WK → List Bool) : ℕ :=
  let S1 := copyExec wN wCnt wTmp1 S
  let S2 := (S1 wCnt).foldl (fun U _ => readOneBitExec U) (Function.update S1 wCnt [])
  (3 * (S2 wTmp2).length + 1) +
    (forEachCost wCnt (fun _ => readOneBitExec) (fun _ _ => 4) (S1 wCnt) S1 +
      (7 * (S wN).length + 4 * (S wTmp1).length + 2))

theorem psb_readRow : PureSB readRowExec readRowCost := by
  unfold readRowExec readRowCost
  exact psb_seq (psb_seq (psb_copy (a := wN) (b := wCnt) (tmp := wTmp1) (by decide) (by decide) (by decide))
    (psb_forEachIgn wCnt psb_readOneBit (indep_readOneBit (by decide) (by decide))))
    (psb_revMove (a := wTmp2) (b := wRow) (by decide))

theorem indep_readRow {k : WK} (h0 : wN ≠ k) (h1 : wCnt ≠ k) (h2 : wTmp1 ≠ k)
    (h3 : wIn ≠ k) (h4 : wTmp2 ≠ k) (h5 : wRow ≠ k) : Indep k readRowExec := by
  unfold readRowExec
  have hf : Indep k (fun S => (S wCnt).foldl (fun U _ => readOneBitExec U) (Function.update S wCnt [])) := by
    intro S l; dsimp only
    rw [Function.update_of_ne h1, Function.update_comm h1.symm]
    generalize S wCnt = lc; generalize Function.update S wCnt [] = U
    induction lc generalizing U with
    | nil => rfl
    | cons _ lc ih => simp only [List.foldl_cons]; rw [indep_readOneBit h3 h4, ih]
  exact indep_seq (indep_seq (indep_copy h0 h1 h2) hf) (indep_revMove h4 h5)

theorem readRow_spec (S : WK → List Bool) (hC : S wCnt = []) (hR : S wRow = [])
    (ht1 : S wTmp1 = []) (ht2 : S wTmp2 = []) :
    readRowExec S =
      Function.update (Function.update S wIn ((S wIn).drop (S wN).length)) wRow
        ((List.range (S wN).length).map (fun i => (S wIn).getD i false)) ∧
    readRowCost S ≤ 16 * (S wN).length + 5 := by
  have hfold : ∀ (l : List Bool) (U : WK → List Bool),
      l.foldl (fun W _ => readOneBitExec W) U =
        Function.update (Function.update U wIn ((U wIn).drop l.length)) wTmp2
          (((List.range l.length).map (fun i => (U wIn).getD i false)).reverse ++ U wTmp2) := by
    intro l
    induction l with
    | nil => intro U; simp [Function.update_eq_self]
    | cons _ l ih =>
      intro U
      simp only [List.foldl_cons, List.length_cons]
      have hst : readOneBitExec U =
          Function.update (Function.update U wIn (U wIn).tail) wTmp2 ((U wIn).getD 0 false :: U wTmp2) := by
        cases hu : U wIn with
        | nil =>
          funext j; simp only [readOneBitExec, hu, List.tail_nil, List.getD_nil]
          by_cases j1 : j = wTmp2; · subst j1; simp [Fin.ext_iff]
          by_cases j2 : j = wIn; · subst j2; simp [Fin.ext_iff]
          simp [Fin.ext_iff, j1, j2]
        | cons b lr =>
          cases b
          · funext j; simp only [readOneBitExec, hu, List.tail_cons, List.getD_cons_zero]
            by_cases j1 : j = wTmp2; · subst j1; simp [Fin.ext_iff]
            by_cases j2 : j = wIn; · subst j2; simp [Fin.ext_iff]
            simp [j1, j2]
          · funext j; simp only [readOneBitExec, hu, List.tail_cons, List.getD_cons_zero]
            by_cases j1 : j = wTmp2; · subst j1; simp [Fin.ext_iff]
            by_cases j2 : j = wIn; · subst j2; simp [Fin.ext_iff]
            simp [j1, j2]
      rw [hst, ih]
      have hdrop : (U wIn).tail.drop l.length = (U wIn).drop (l.length + 1) := by
        cases U wIn <;> simp
      have hrange : (List.range (l.length + 1)).map (fun i => (U wIn).getD i false) =
          (U wIn).getD 0 false :: (List.range l.length).map (fun i => (U wIn).tail.getD i false) := by
        rw [List.range_succ_eq_map, List.map_cons, List.map_map]
        congr 1; apply List.map_congr_left; intro i _
        cases U wIn <;> simp
      funext j
      by_cases j1 : j = wTmp2
      · subst j1; simp only [Function.update_self, hrange, List.reverse_cons, List.append_assoc]; rfl
      by_cases j2 : j = wIn
      · subst j2; simp [Fin.ext_iff, hdrop]
      simp [Fin.ext_iff, j1, j2]
  have hS1 : copyExec wN wCnt wTmp1 S = Function.update S wCnt (S wN) := by
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S ht1, hC, List.append_nil]
  have hS2 : ((copyExec wN wCnt wTmp1 S) wCnt).foldl (fun U _ => readOneBitExec U)
      (Function.update (copyExec wN wCnt wTmp1 S) wCnt []) =
      Function.update (Function.update S wIn ((S wIn).drop (S wN).length)) wTmp2
        ((List.range (S wN).length).map (fun i => (S wIn).getD i false)).reverse := by
    rw [hS1]; simp only [Function.update_self]
    rw [hfold]
    funext j
    by_cases j1 : j = wTmp2; · subst j1; simp [Fin.ext_iff, ht2]
    by_cases j2 : j = wIn; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = wCnt; · subst j3; simp [Fin.ext_iff, hC]
    simp [Fin.ext_iff, j1, j2, j3]
  refine ⟨?_, ?_⟩
  · simp only [readRowExec, hS2, revMoveExec]
    funext j
    by_cases j1 : j = wRow; · subst j1; simp [Fin.ext_iff, hR]
    by_cases j2 : j = wTmp2; · subst j2; simp [Fin.ext_iff, ht2]
    by_cases j3 : j = wIn; · subst j3; simp [Fin.ext_iff]
    simp [Fin.ext_iff, j1, j2, j3]
  · simp only [readRowCost, hS2]
    have hfc := forEachCost_le wCnt (fun _ => readOneBitExec) (fun _ _ => 4) (fun _ => True) 4
      (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial)
      (copyExec wN wCnt wTmp1 S wCnt) (copyExec wN wCnt wTmp1 S) trivial
    rw [hS1] at hfc ⊢
    simp only [Function.update_self, List.length_reverse, List.length_map, List.length_range,
      ht1, List.length_nil] at hfc ⊢
    omega

def rowStepExec (b : Bool) (S : WK → List Bool) : WK → List Bool :=
  let S1 := if b then incFixedExec wY wTmp1 S else incFixedExec wY wTmp1 (emitPairExec S)
  emitManyExec (copyExec wL wCnt wTmp1 S1)

def rowStepCost (b : Bool) (S : WK → List Bool) : ℕ :=
  let S1 := if b then incFixedExec wY wTmp1 S else incFixedExec wY wTmp1 (emitPairExec S)
  let c1 := if b then 5 * (S wY).length + 3 * (S wTmp1).length + 7 else emitOneCost S
  (emitManyCost (copyExec wL wCnt wTmp1 S1) + (7 * (S1 wL).length + 4 * (S1 wTmp1).length + 2)) + c1

theorem psb_rowStep (b : Bool) : PureSB (rowStepExec b) (rowStepCost b) := by
  unfold rowStepExec rowStepCost
  have htail := psb_seq (psb_copy (a := wL) (b := wCnt) (tmp := wTmp1) (by decide) (by decide) (by decide)) psb_emitMany
  cases b
  · exact psb_seq psb_emitOne htail
  · exact psb_seq (psb_incFixed (x := wY) (tmp := wTmp1) (by decide)) htail

theorem indep_rowStep {k : WK} (h0 : wX ≠ k) (h1 : wY ≠ k) (h2 : wOutRev ≠ k)
    (h3 : wTmp1 ≠ k) (h4 : wL ≠ k) (h5 : wCnt ≠ k) (b : Bool) :
    Indep k (rowStepExec b) := by
  unfold rowStepExec
  have ht := indep_seq (indep_copy h4 h5 h3) (indep_emitMany h5 h0 h1 h2 h3)
  cases b
  · exact indep_seq (indep_emitOne h0 h1 h2 h3) ht
  · exact indep_seq (indep_incFixed h1 h3) ht

theorem rowStep_spec (b : Bool) (S : WK → List Bool) (w x y : ℕ)
    (hX : S wX = fieldBits w x) (hY : S wY = fieldBits w y) (hC : S wCnt = []) (ht : S wTmp1 = []) :
    rowStepExec b S =
      Function.update (Function.update S wOutRev
        (((if b then [] else emitPairBits w x y) ++ emitRange w x (y + 1) (S wL).length).reverse ++ S wOutRev))
        wY (fieldBits w (y + ((S wL).length + 1))) ∧
    rowStepCost b S ≤ ((S wL).length + 1) * (19 * w + 20) + 5 := by
  have hS1 : (if b then incFixedExec wY wTmp1 S else incFixedExec wY wTmp1 (emitPairExec S)) =
      Function.update (Function.update S wOutRev ((if b then [] else emitPairBits w x y).reverse ++ S wOutRev))
        wY (fieldBits w (y + 1)) ∧
      (if b then 5 * (S wY).length + 3 * (S wTmp1).length + 7 else emitOneCost S) ≤ 19 * w + 11 := by
    cases b
    · have h1 := emitOne_spec S w x y hX hY ht
      exact ⟨h1.1, h1.2⟩
    · refine ⟨?_, ?_⟩
      · rw [incFixedExec_of_empty (by decide) S ht, hY, incFixedBits_fieldBits]
        funext j
        by_cases j1 : j = wY; · subst j1; simp [Fin.ext_iff]
        by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff]
        simp [Fin.ext_iff, j1, j2]
      · simp [hY, ht, fieldBits_length]; omega
  let S1 := if b then incFixedExec wY wTmp1 S else incFixedExec wY wTmp1 (emitPairExec S)
  have hcp : copyExec wL wCnt wTmp1 S1 = Function.update S1 wCnt (S wL) := by
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S1 (by simp only [S1]; rw [hS1.1]; simp [Fin.ext_iff, ht])]
    simp only [S1]; rw [hS1.1]; simp [Fin.ext_iff, hC]
  have hm := emitMany_spec (copyExec wL wCnt wTmp1 S1) w x (y + 1)
    (by rw [hcp]; simp only [S1]; rw [hS1.1]; simp [Fin.ext_iff, hX])
    (by rw [hcp]; simp only [S1]; rw [hS1.1]; simp [Fin.ext_iff])
    (by rw [hcp]; simp only [S1]; rw [hS1.1]; simp [Fin.ext_iff, ht])
  refine ⟨?_, ?_⟩
  · simp only [rowStepExec]
    change emitManyExec (copyExec wL wCnt wTmp1 S1) = _
    rw [hm.1, hcp]
    simp only [S1]
    rw [hS1.1]
    funext j
    by_cases j1 : j = wY
    · subst j1; simp [Fin.ext_iff, show y + 1 + (S wL).length = y + ((S wL).length + 1) by omega]
    by_cases j2 : j = wOutRev
    · subst j2; simp [Fin.ext_iff, List.reverse_append, List.append_assoc]
    by_cases j3 : j = wCnt
    · subst j3; simp [Fin.ext_iff, hC]
    simp [Fin.ext_iff, j1, j2, j3]
  · simp only [rowStepCost]
    have hm2 := hm.2
    have hc1 := hS1.2
    rw [hcp] at hm2 ⊢
    simp only [S1] at hm2 ⊢
    rw [hS1.1] at hm2 ⊢
    simp only [Function.update_self, Function.update_of_ne (by decide : wL ≠ wY),
      Function.update_of_ne (by decide : wL ≠ wOutRev),
      Function.update_of_ne (by decide : wTmp1 ≠ wY),
      Function.update_of_ne (by decide : wTmp1 ≠ wOutRev), ht, List.length_nil] at hm2 hc1 ⊢
    have hmul : ((S wL).length + 1) * (19 * w + 20) =
        (S wL).length * (19 * w + 13) + 7 * (S wL).length + (19 * w + 20) := by ring
    omega

def leftRx0Exec (S : WK → List Bool) : WK → List Bool :=
  let S1 := copyExec wX wY wTmp1 S
  let S2 := incFixedExec wY wTmp1 S1
  let S3 := incFixedExec wY wTmp1 S2
  let S4 := copyExec wLm1 wCnt wTmp1 S3
  let S5 := emitManyExec S4
  let S6 := copyExec wRemLeft wBlk wTmp1 S5
  let S7 := emitBlocksExec S6
  let S8 := (S7 wRow).foldl (fun U b => rowStepExec b U) (Function.update S7 wRow [])
  let S9 := clearExec wY S8
  incFixedExec wX wTmp1 S9

def leftRx0Cost (S : WK → List Bool) : ℕ :=
  let S1 := copyExec wX wY wTmp1 S
  let S2 := incFixedExec wY wTmp1 S1
  let S3 := incFixedExec wY wTmp1 S2
  let S4 := copyExec wLm1 wCnt wTmp1 S3
  let S5 := emitManyExec S4
  let S6 := copyExec wRemLeft wBlk wTmp1 S5
  let S7 := emitBlocksExec S6
  let S8 := (S7 wRow).foldl (fun U b => rowStepExec b U) (Function.update S7 wRow [])
  let S9 := clearExec wY S8
  (5 * (S9 wX).length + 3 * (S9 wTmp1).length + 7) +
    ((3 * (S8 wY).length + 1) +
      (forEachCost wRow rowStepExec rowStepCost (S7 wRow) S7 +
        (emitBlocksCost S6 +
          ((7 * (S5 wRemLeft).length + 4 * (S5 wTmp1).length + 2) +
            (emitManyCost S4 +
              ((7 * (S3 wLm1).length + 4 * (S3 wTmp1).length + 2) +
                ((5 * (S2 wY).length + 3 * (S2 wTmp1).length + 7) +
                  ((5 * (S1 wY).length + 3 * (S1 wTmp1).length + 7) +
                    (7 * (S wX).length + 4 * (S wTmp1).length + 2)))))))))

theorem psb_leftRx0 : PureSB leftRx0Exec leftRx0Cost := by
  have h1 := psb_copy (a := wX) (b := wY) (tmp := wTmp1) (by decide) (by decide) (by decide)
  have h2 := psb_seq h1 (psb_incFixed (x := wY) (tmp := wTmp1) (by decide))
  have h3 := psb_seq h2 (psb_incFixed (x := wY) (tmp := wTmp1) (by decide))
  have h4 := psb_seq h3 (psb_copy (a := wLm1) (b := wCnt) (tmp := wTmp1) (by decide) (by decide) (by decide))
  have h5 := psb_seq h4 psb_emitMany
  have h6 := psb_seq h5 (psb_copy (a := wRemLeft) (b := wBlk) (tmp := wTmp1) (by decide) (by decide) (by decide))
  have h7 := psb_seq h6 psb_emitBlocks
  have h8 := psb_seq h7 (psb_forEach wRow (B := rowStepCost) (psb_rowStep false) (psb_rowStep true)
    (fun b => indep_rowStep (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) b))
  have h9 := psb_seq h8 (psb_clear wY)
  have h10 := psb_seq h9 (psb_incFixed (x := wX) (tmp := wTmp1) (by decide))
  exact h10

theorem indep_leftRx0 {k : WK} (hx : wX ≠ k) (hy : wY ≠ k) (ht : wTmp1 ≠ k) (hlm : wLm1 ≠ k)
    (hc : wCnt ≠ k) (ho : wOutRev ≠ k) (hrl : wRemLeft ≠ k) (hb : wBlk ≠ k)
    (hl1 : wL1 ≠ k) (hrow : wRow ≠ k) (hl : wL ≠ k) : Indep k leftRx0Exec := by
  have hrf : Indep k (fun S => (S wRow).foldl (fun U b => rowStepExec b U) (Function.update S wRow [])) := by
    intro S l; dsimp only
    rw [Function.update_of_ne hrow, Function.update_comm hrow.symm]
    generalize S wRow = lr; generalize Function.update S wRow [] = U
    induction lr generalizing U with
    | nil => rfl
    | cons b lr ih => simp only [List.foldl_cons]; rw [indep_rowStep hx hy ho ht hl hc b, ih]
  have h1 := indep_copy hx hy ht
  have h2 := indep_seq h1 (indep_incFixed hy ht)
  have h3 := indep_seq h2 (indep_incFixed hy ht)
  have h4 := indep_seq h3 (indep_copy hlm hc ht)
  have h5 := indep_seq h4 (indep_emitMany hc hx hy ho ht)
  have h6 := indep_seq h5 (indep_copy hrl hb ht)
  have h7 := indep_seq h6 (indep_emitBlocks hb hl1 hc hx hy ho ht)
  have h8 := indep_seq h7 hrf
  have h9 := indep_seq h8 (indep_clear hy)
  have h10 := indep_seq h9 (indep_incFixed hx ht)
  exact h10

theorem leftRx0_spec (S : WK → List Bool) (w x L : ℕ) (hL2 : 2 ≤ L)
    (hL : (S wL).length = L) (hL1 : (S wL1).length = L + 1) (hLm1 : (S wLm1).length = L - 1)
    (hX : S wX = fieldBits w x) (hY : S wY = []) (hC : S wCnt = []) (hB : S wBlk = [])
    (ht : S wTmp1 = []) :
    leftRx0Exec S =
      Function.update (Function.update (Function.update S wRow [])
        wOutRev ((emitLeftRx0 w x L (S wRemLeft).length (S wRow)).reverse ++ S wOutRev))
        wX (fieldBits w (x + 1)) ∧
    leftRx0Cost S ≤
      (L + (S wRemLeft).length * (L + 1) + (S wRow).length * (L + 1)) * (19 * w + 20) +
        12 * (S wRemLeft).length + 7 * (S wRow).length + 7 * L + 25 * w + 40 := by
  have hS1 : copyExec wX wY wTmp1 S = Function.update S wY (fieldBits w x) := by
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S ht, hX, hY, List.append_nil]
  have hS2 : incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S) = Function.update S wY (fieldBits w (x + 1)) := by
    rw [hS1, incFixedExec_of_empty (by decide) _ (by simp [Fin.ext_iff, ht]),
        Function.update_self, incFixedBits_fieldBits, Function.update_idem]
  have hS3 : incFixedExec wY wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S)) =
      Function.update S wY (fieldBits w (x + 2)) := by
    rw [hS2, incFixedExec_of_empty (by decide) _ (by simp [Fin.ext_iff, ht]),
        Function.update_self, incFixedBits_fieldBits, Function.update_idem,
        show x + 1 + 1 = x + 2 by omega]
  have hS4 : copyExec wLm1 wCnt wTmp1 (incFixedExec wY wTmp1 (incFixedExec wY wTmp1 (copyExec wX wY wTmp1 S))) =
      Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1) := by
    rw [hS3, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, ht])]
    simp [Fin.ext_iff, hC]
  have hm5 := emitMany_spec
    (Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1))
    w x (x + 2) (by simp [Fin.ext_iff, hX]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff, ht])
  have hS5 : emitManyExec (Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1)) =
      Function.update (Function.update S wOutRev ((emitRange w x (x + 2) (L - 1)).reverse ++ S wOutRev))
        wY (fieldBits w (x + L + 1)) := by
    rw [hm5.1]
    simp only [Function.update_self, hLm1, show x + 2 + (L - 1) = x + L + 1 by omega]
    funext j
    by_cases j1 : j = wY; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = wCnt; · subst j3; simp [Fin.ext_iff, hC]
    simp [Fin.ext_iff, j1, j2, j3]
  have hS6 : copyExec wRemLeft wBlk wTmp1
      (emitManyExec (Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1))) =
      Function.update (Function.update (Function.update S wOutRev ((emitRange w x (x + 2) (L - 1)).reverse ++ S wOutRev))
        wY (fieldBits w (x + L + 1))) wBlk (S wRemLeft) := by
    rw [hS5, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, ht])]
    simp [Fin.ext_iff, hB]
  have hb7 := emitBlocks_spec
    (Function.update (Function.update (Function.update S wOutRev ((emitRange w x (x + 2) (L - 1)).reverse ++ S wOutRev))
      wY (fieldBits w (x + L + 1))) wBlk (S wRemLeft))
    w x (x + L + 1) (by simp [Fin.ext_iff, hX]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff, hC])
    (by simp [Fin.ext_iff, ht])
  have hS7 : emitBlocksExec (copyExec wRemLeft wBlk wTmp1
      (emitManyExec (Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1)))) =
      Function.update (Function.update S wOutRev
        ((emitRange w x (x + 2) (L - 1) ++ emitRange w x (x + L + 1) ((S wRemLeft).length * (L + 1))).reverse ++ S wOutRev))
        wY (fieldBits w (x + L + 1 + (S wRemLeft).length * (L + 1))) := by
    rw [hS6, hb7.1]
    funext j
    by_cases j1 : j = wY; · subst j1; simp [Fin.ext_iff, hL1]
    by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff, hL1, List.reverse_append, List.append_assoc]
    by_cases j3 : j = wBlk; · subst j3; simp [Fin.ext_iff, hB]
    simp [Fin.ext_iff, j1, j2, j3]
  have hrowFold : ∀ (lr : List Bool) (y0 : ℕ) (U : WK → List Bool),
      (U wL).length = L → U wX = fieldBits w x → U wY = fieldBits w y0 → U wCnt = [] → U wTmp1 = [] →
      lr.foldl (fun W b => rowStepExec b W) U =
        Function.update (Function.update U wOutRev ((emitRow w x y0 L lr).reverse ++ U wOutRev))
          wY (fieldBits w (y0 + lr.length * (L + 1))) ∧
      forEachCost wRow rowStepExec rowStepCost lr U ≤
        lr.length * ((L + 1) * (19 * w + 20) + 7) + 1 := by
    intro lr
    induction lr with
    | nil =>
      intro y0 U _ _ hUY _ _
      refine ⟨?_, by simp [forEachCost]⟩
      funext j
      by_cases j1 : j = wY; · subst j1; simp [Fin.ext_iff, hUY]
      by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff, emitRow]
      simp [Fin.ext_iff, j1, j2]
    | cons b lr ih =>
      intro y0 U hUL hUX hUY hUC hUt
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have h1 := rowStep_spec b U w x y0 hUX hUY hUC hUt
      have h1' := rowStep_spec b (Function.update U wRow lr) w x y0
        (by simp [Fin.ext_iff, hUX]) (by simp [Fin.ext_iff, hUY]) (by simp [Fin.ext_iff, hUC]) (by simp [Fin.ext_iff, hUt])
      have hr1 := ih (y0 + (L + 1)) (rowStepExec b U)
        (by rw [h1.1]; simp [Fin.ext_iff, hUL]) (by rw [h1.1]; simp [Fin.ext_iff, hUX])
        (by rw [h1.1]; simp [Fin.ext_iff, hUL]) (by rw [h1.1]; simp [Fin.ext_iff, hUC])
        (by rw [h1.1]; simp [Fin.ext_iff, hUt])
      have hr2 := ih (y0 + (L + 1)) (rowStepExec b (Function.update U wRow lr))
        (by rw [h1'.1]; simp [Fin.ext_iff, hUL]) (by rw [h1'.1]; simp [Fin.ext_iff, hUX])
        (by rw [h1'.1]; simp [Fin.ext_iff, hUL]) (by rw [h1'.1]; simp [Fin.ext_iff, hUC])
        (by rw [h1'.1]; simp [Fin.ext_iff, hUt])
      refine ⟨?_, ?_⟩
      · rw [hr1.1, h1.1, hUL]
        funext j
        by_cases j1 : j = wY
        · subst j1; simp [Fin.ext_iff, show y0 + (L + 1) + lr.length * (L + 1) = y0 + (lr.length + 1) * (L + 1) by ring]
        by_cases j2 : j = wOutRev
        · subst j2; simp [Fin.ext_iff, emitRow, List.reverse_append, List.append_assoc]
        simp [Fin.ext_iff, j1, j2]
      · have hc1 := h1'.2
        simp only [Function.update_of_ne (by decide : wL ≠ wRow), hUL] at hc1
        have hc2 := hr2.2
        have hmul : (lr.length + 1) * ((L + 1) * (19 * w + 20) + 7) =
            lr.length * ((L + 1) * (19 * w + 20) + 7) + ((L + 1) * (19 * w + 20) + 7) := by ring
        omega
  set yRow := x + L + 1 + (S wRemLeft).length * (L + 1)
  have hS7r : (emitBlocksExec (copyExec wRemLeft wBlk wTmp1
      (emitManyExec (Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1))))) wRow = S wRow := by
    rw [hS7]; simp [Fin.ext_iff]
  have hrf1 := hrowFold (S wRow) yRow (Function.update (emitBlocksExec (copyExec wRemLeft wBlk wTmp1
      (emitManyExec (Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1))))) wRow [])
    (by rw [hS7]; simp [Fin.ext_iff, hL]) (by rw [hS7]; simp [Fin.ext_iff, hX])
    (by rw [hS7]; simp [Fin.ext_iff, yRow]) (by rw [hS7]; simp [Fin.ext_iff, hC])
    (by rw [hS7]; simp [Fin.ext_iff, ht])
  have hrf2 := hrowFold (S wRow) yRow (emitBlocksExec (copyExec wRemLeft wBlk wTmp1
      (emitManyExec (Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1)))))
    (by rw [hS7]; simp [Fin.ext_iff, hL]) (by rw [hS7]; simp [Fin.ext_iff, hX])
    (by rw [hS7]; simp [Fin.ext_iff, yRow]) (by rw [hS7]; simp [Fin.ext_iff, hC])
    (by rw [hS7]; simp [Fin.ext_iff, ht])
  have hS8 : ((emitBlocksExec (copyExec wRemLeft wBlk wTmp1
      (emitManyExec (Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1))))) wRow).foldl
      (fun U b => rowStepExec b U)
      (Function.update (emitBlocksExec (copyExec wRemLeft wBlk wTmp1
        (emitManyExec (Function.update (Function.update S wY (fieldBits w (x + 2))) wCnt (S wLm1))))) wRow []) =
      Function.update (Function.update (Function.update S wRow []) wOutRev
        ((emitLeftRx0 w x L (S wRemLeft).length (S wRow)).reverse ++ S wOutRev))
        wY (fieldBits w (yRow + (S wRow).length * (L + 1))) := by
    rw [hS7r, hrf1.1, hS7]
    funext j
    by_cases j1 : j = wY; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = wOutRev
    · subst j2; simp [Fin.ext_iff, emitLeftRx0, yRow, List.reverse_append, List.append_assoc]
    by_cases j3 : j = wRow; · subst j3; simp [Fin.ext_iff]
    simp [Fin.ext_iff, j1, j2, j3]
  refine ⟨?_, ?_⟩
  · simp only [leftRx0Exec]
    rw [hS4, hS8]
    rw [incFixedExec_of_empty (by decide) _ (by simp [clearExec, Fin.ext_iff, ht])]
    funext j
    by_cases j1 : j = wX; · subst j1; simp [clearExec, Fin.ext_iff, hX, incFixedBits_fieldBits]
    by_cases j2 : j = wOutRev; · subst j2; simp [clearExec, Fin.ext_iff]
    by_cases j3 : j = wRow; · subst j3; simp [clearExec, Fin.ext_iff]
    by_cases j4 : j = wY; · subst j4; simp [clearExec, Fin.ext_iff, hY]
    simp [clearExec, Fin.ext_iff, j1, j2, j3, j4]
  · simp only [leftRx0Cost]
    rw [hS4, hS8]
    have hc5 := hm5.2; simp only [Function.update_self, hLm1] at hc5
    have hc7 := hb7.2; simp only [Function.update_self, Function.update_of_ne (by decide : wL1 ≠ wBlk),
      Function.update_of_ne (by decide : wL1 ≠ wY), Function.update_of_ne (by decide : wL1 ≠ wOutRev), hL1] at hc7
    have hc8 := hrf2.2
    rw [hS7r]
    rw [hS6] at hc8 ⊢
    rw [hS5, hS3, hS2, hS1]
    simp only [clearExec, Function.update_self,
      Function.update_of_ne (by decide : wX ≠ wY), Function.update_of_ne (by decide : wX ≠ wOutRev),
      Function.update_of_ne (by decide : wX ≠ wRow), Function.update_of_ne (by decide : wTmp1 ≠ wY),
      Function.update_of_ne (by decide : wTmp1 ≠ wOutRev), Function.update_of_ne (by decide : wTmp1 ≠ wRow),
      Function.update_of_ne (by decide : wRemLeft ≠ wY), Function.update_of_ne (by decide : wRemLeft ≠ wOutRev),
      Function.update_of_ne (by decide : wLm1 ≠ wY), hX, ht, hLm1, fieldBits_length, List.length_nil] at hc8 ⊢
    have h1 : (L - 1) * (19 * w + 13) ≤ L * (19 * w + 20) :=
      Nat.mul_le_mul (Nat.sub_le L 1) (by omega)
    have h2 : (S wRemLeft).length * ((L + 1) * (19 * w + 20) + 5) =
        (S wRemLeft).length * (L + 1) * (19 * w + 20) + 5 * (S wRemLeft).length := by ring
    have h3 : (S wRow).length * ((L + 1) * (19 * w + 20) + 7) =
        (S wRow).length * (L + 1) * (19 * w + 20) + 7 * (S wRow).length := by ring
    have h4 : (L + (S wRemLeft).length * (L + 1) + (S wRow).length * (L + 1)) * (19 * w + 20) =
        L * (19 * w + 20) + (S wRemLeft).length * (L + 1) * (19 * w + 20) +
        (S wRow).length * (L + 1) * (19 * w + 20) := by ring
    omega

def leftBlockExec (S : WK → List Bool) : WK → List Bool :=
  let S1 := Function.update S wRemLeft (S wRemLeft).tail
  let S2 := Function.update S1 wRemAll (S1 wRemAll).tail
  let S3 := readRowExec S2
  let S4 := leftRx0Exec S3
  let S5 := copyExec wL wRemR wTmp1 S4
  let S6 := copyExec wL wRxLoop wTmp1 S5
  noBaseLoopExec S6

def leftBlockCost (S : WK → List Bool) : ℕ :=
  let S1 := Function.update S wRemLeft (S wRemLeft).tail
  let S2 := Function.update S1 wRemAll (S1 wRemAll).tail
  let S3 := readRowExec S2
  let S4 := leftRx0Exec S3
  let S5 := copyExec wL wRemR wTmp1 S4
  let S6 := copyExec wL wRxLoop wTmp1 S5
  noBaseLoopCost S6 +
    ((7 * (S5 wL).length + 4 * (S5 wTmp1).length + 2) +
      ((7 * (S4 wL).length + 4 * (S4 wTmp1).length + 2) +
        (leftRx0Cost S3 + (readRowCost S2 + 2))))

theorem psb_leftBlock : PureSB leftBlockExec leftBlockCost := by
  have h1 := psb_popDrop wRemLeft
  have h2 := psb_seq h1 (psb_popDrop wRemAll)
  have h3 := psb_seq h2 psb_readRow
  have h4 := psb_seq h3 psb_leftRx0
  have h5 := psb_seq h4 (psb_copy (a := wL) (b := wRemR) (tmp := wTmp1) (by decide) (by decide) (by decide))
  have h6 := psb_seq h5 (psb_copy (a := wL) (b := wRxLoop) (tmp := wTmp1) (by decide) (by decide) (by decide))
  have h7 := psb_seq h6 psb_noBaseLoop
  exact h7

theorem indep_leftBlock : Indep wNloop leftBlockExec := by
  have h1 := indep_popDrop (k := wNloop) (k' := wRemLeft) (by decide)
  have h2 := indep_seq h1 (indep_popDrop (k := wNloop) (k' := wRemAll) (by decide))
  have h3 := indep_seq h2 (indep_readRow (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have h4 := indep_seq h3 (indep_leftRx0 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have h5 := indep_seq h4 (indep_copy (a := wL) (b := wRemR) (tmp := wTmp1) (by decide) (by decide) (by decide))
  have h6 := indep_seq h5 (indep_copy (a := wL) (b := wRxLoop) (tmp := wTmp1) (by decide) (by decide) (by decide))
  have h7 := indep_seq h6 (indep_noBaseLoop (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide))
  exact h7

def rightBlockExec (S : WK → List Bool) : WK → List Bool :=
  let S1 := Function.update S wRemAll (S wRemAll).tail
  let S2 := copyExec wL1 wRemR wTmp1 S1
  let S3 := copyExec wL1 wRxLoop wTmp1 S2
  noBaseLoopExec S3

def rightBlockCost (S : WK → List Bool) : ℕ :=
  let S1 := Function.update S wRemAll (S wRemAll).tail
  let S2 := copyExec wL1 wRemR wTmp1 S1
  let S3 := copyExec wL1 wRxLoop wTmp1 S2
  noBaseLoopCost S3 +
    ((7 * (S2 wL1).length + 4 * (S2 wTmp1).length + 2) +
      ((7 * (S1 wL1).length + 4 * (S1 wTmp1).length + 2) + 1))

theorem psb_rightBlock : PureSB rightBlockExec rightBlockCost := by
  unfold rightBlockExec rightBlockCost
  exact psb_seq
    (psb_seq
      (psb_seq (psb_popDrop wRemAll) (psb_copy (a := wL1) (b := wRemR) (tmp := wTmp1) (by decide) (by decide) (by decide)))
      (psb_copy (a := wL1) (b := wRxLoop) (tmp := wTmp1) (by decide) (by decide) (by decide)))
    psb_noBaseLoop

theorem indep_rightBlock : Indep wNloop rightBlockExec := by
  unfold rightBlockExec
  exact indep_seq
    (indep_seq
      (indep_seq (indep_popDrop (k' := wRemAll) (by decide))
        (indep_copy (a := wL1) (b := wRemR) (tmp := wTmp1) (by decide) (by decide) (by decide)))
      (indep_copy (a := wL1) (b := wRxLoop) (tmp := wTmp1) (by decide) (by decide) (by decide)))
    (indep_noBaseLoop (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))

theorem leftBlock_spec (S : WK → List Bool) (w x L n m remAll : ℕ) (hL2 : 2 ≤ L)
    (hN : (S wN).length = n) (hL : (S wL).length = L) (hL1 : (S wL1).length = L + 1)
    (hLm1 : (S wLm1).length = L - 1) (hRL : (S wRemLeft).length = m + 1)
    (hRA : (S wRemAll).length = remAll + 1) (hX : S wX = fieldBits w x)
    (hY : S wY = []) (hRR : S wRemR = []) (hRow : S wRow = []) (hC : S wCnt = [])
    (hB : S wBlk = []) (hRx : S wRxLoop = []) (ht1 : S wTmp1 = []) (ht2 : S wTmp2 = []) :
    let row := (List.range n).map (fun i => (S wIn).getD i false)
    leftBlockExec S =
      Function.update (Function.update (Function.update (Function.update (Function.update S
        wRemLeft (S wRemLeft).tail) wRemAll (S wRemAll).tail) wIn ((S wIn).drop n))
        wOutRev ((emitLeftRx0 w x L m row ++ emitNoBaseLoop w (x + 1) remAll (L + 1) L).reverse ++ S wOutRev))
        wX (fieldBits w (x + L + 1)) ∧
    leftBlockCost S ≤
      (L + 1) * ((L + 1 + (m + n + remAll) * (L + 1)) * (19 * w + 20) +
        12 * (m + n + remAll) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 20 := by
  intro row
  let S1 := Function.update S wRemLeft (S wRemLeft).tail
  let S2 := Function.update S1 wRemAll (S1 wRemAll).tail
  have hS2RL : (S2 wRemLeft).length = m := by simp [S2, S1, Fin.ext_iff, hRL]
  have hS2RA : (S2 wRemAll).length = remAll := by simp [S2, S1, Fin.ext_iff, hRA]
  have hRR3 := readRow_spec S2 (by simp [S2, S1, Fin.ext_iff, hC]) (by simp [S2, S1, Fin.ext_iff, hRow])
    (by simp [S2, S1, Fin.ext_iff, ht1]) (by simp [S2, S1, Fin.ext_iff, ht2])
  have hS3 : readRowExec S2 = Function.update (Function.update S2 wIn ((S wIn).drop n)) wRow row := by
    rw [hRR3.1]; simp [S2, S1, Fin.ext_iff, hN, row]
  have hRx4 := leftRx0_spec (readRowExec S2) w x L hL2
    (by rw [hS3]; simp [S2, S1, Fin.ext_iff, hL]) (by rw [hS3]; simp [S2, S1, Fin.ext_iff, hL1])
    (by rw [hS3]; simp [S2, S1, Fin.ext_iff, hLm1]) (by rw [hS3]; simp [S2, S1, Fin.ext_iff, hX])
    (by rw [hS3]; simp [S2, S1, Fin.ext_iff, hY]) (by rw [hS3]; simp [S2, S1, Fin.ext_iff, hC])
    (by rw [hS3]; simp [S2, S1, Fin.ext_iff, hB]) (by rw [hS3]; simp [S2, S1, Fin.ext_iff, ht1])
  have hS4 : leftRx0Exec (readRowExec S2) =
      Function.update (Function.update (Function.update S2 wIn ((S wIn).drop n))
        wOutRev ((emitLeftRx0 w x L m row).reverse ++ S wOutRev))
        wX (fieldBits w (x + 1)) := by
    rw [hRx4.1, hS3]
    funext j
    by_cases j1 : j = wX; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = wOutRev; · subst j2; simp [S2, S1, Fin.ext_iff, hRL]
    by_cases j3 : j = wRow; · subst j3; simp [S2, S1, Fin.ext_iff, hRow]
    by_cases j4 : j = wIn; · subst j4; simp [Fin.ext_iff]
    simp [Fin.ext_iff, j1, j2, j3, j4]
  have hS5 : copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2)) =
      Function.update (leftRx0Exec (readRowExec S2)) wRemR (S wL) := by
    rw [copyExec_of_empty (by decide) (by decide) (by decide) _ (by rw [hS4]; simp [S2, S1, Fin.ext_iff, ht1])]
    rw [hS4]; simp [S2, S1, Fin.ext_iff, hRR]
  have hS6 : copyExec wL wRxLoop wTmp1 (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2))) =
      Function.update (Function.update (leftRx0Exec (readRowExec S2)) wRemR (S wL)) wRxLoop (S wL) := by
    rw [hS5, copyExec_of_empty (by decide) (by decide) (by decide) _ (by rw [hS4]; simp [S2, S1, Fin.ext_iff, ht1])]
    rw [hS4]; simp [S2, S1, Fin.ext_iff, hRx]
  have hNB := noBaseLoop_spec (copyExec wL wRxLoop wTmp1 (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2))))
    w (x + 1) (by rw [hS6]; simp [Fin.ext_iff]) (by rw [hS6, hS4]; simp [Fin.ext_iff])
    (by rw [hS6, hS4]; simp [S2, S1, Fin.ext_iff, hY]) (by rw [hS6, hS4]; simp [S2, S1, Fin.ext_iff, hC])
    (by rw [hS6, hS4]; simp [S2, S1, Fin.ext_iff, hB]) (by rw [hS6, hS4]; simp [S2, S1, Fin.ext_iff, ht1])
  refine ⟨?_, ?_⟩
  · simp only [leftBlockExec]
    change noBaseLoopExec (copyExec wL wRxLoop wTmp1 (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2)))) = _
    rw [hNB.1, hS6, hS4]
    funext j
    by_cases j1 : j = wX
    · subst j1; simp [Fin.ext_iff, hL, show x + 1 + L = x + L + 1 by omega]
    by_cases j2 : j = wOutRev
    · subst j2; simp [S2, S1, Fin.ext_iff, hL, hL1, hRA, List.reverse_append, List.append_assoc]
    by_cases j3 : j = wRemR; · subst j3; simp [S2, S1, Fin.ext_iff, hRR]
    by_cases j4 : j = wRxLoop; · subst j4; simp [S2, S1, Fin.ext_iff, hRx]
    by_cases j5 : j = wIn; · subst j5; simp [Fin.ext_iff]
    by_cases j6 : j = wRemAll; · subst j6; simp [S2, S1, Fin.ext_iff]
    by_cases j7 : j = wRemLeft; · subst j7; simp [S2, S1, Fin.ext_iff]
    simp [S2, S1, Fin.ext_iff, j1, j2, j3, j4, j5, j6, j7]
  · simp only [leftBlockCost]
    change noBaseLoopCost (copyExec wL wRxLoop wTmp1 (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2)))) +
      ((7 * (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2)) wL).length +
        4 * (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2)) wTmp1).length + 2) +
       ((7 * (leftRx0Exec (readRowExec S2) wL).length + 4 * (leftRx0Exec (readRowExec S2) wTmp1).length + 2) +
        (leftRx0Cost (readRowExec S2) + (readRowCost S2 + 2)))) ≤ _
    have hc3 := hRR3.2
    have hS2N : (S2 wN).length = n := by simp [S2, S1, Fin.ext_iff, hN]
    rw [hS2N] at hc3
    have hc4 := hRx4.2
    have hS3RL : (readRowExec S2 wRemLeft).length = m := by rw [hS3]; simp [Fin.ext_iff, hS2RL]
    have hS3Row : (readRowExec S2 wRow).length = n := by rw [hS3]; simp [Fin.ext_iff, row]
    rw [hS3RL, hS3Row] at hc4
    have hc7 := hNB.2
    have hS6Rx : (copyExec wL wRxLoop wTmp1 (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2))) wRxLoop).length = L := by
      rw [hS6]; simp [hL]
    have hS6RA : (copyExec wL wRxLoop wTmp1 (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2))) wRemAll).length = remAll := by
      rw [hS6, hS4]; simp [Fin.ext_iff, hS2RA]
    have hS6L1 : (copyExec wL wRxLoop wTmp1 (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2))) wL1).length = L + 1 := by
      rw [hS6, hS4]; simp [S2, S1, Fin.ext_iff, hL1]
    rw [hS6Rx, hS6RA, hS6L1] at hc7
    have hS5L : (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2)) wL).length = L := by
      rw [hS5, hS4]; simp [S2, S1, Fin.ext_iff, hL]
    have hS5t : (copyExec wL wRemR wTmp1 (leftRx0Exec (readRowExec S2)) wTmp1).length = 0 := by
      rw [hS5, hS4]; simp [S2, S1, Fin.ext_iff, ht1]
    have hS4L : (leftRx0Exec (readRowExec S2) wL).length = L := by
      rw [hS4]; simp [S2, S1, Fin.ext_iff, hL]
    have hS4t : (leftRx0Exec (readRowExec S2) wTmp1).length = 0 := by
      rw [hS4]; simp [S2, S1, Fin.ext_iff, ht1]
    rw [hS5L, hS5t, hS4L, hS4t]
    set P := (L + 1 + (m + n + remAll) * (L + 1)) * (19 * w + 20) +
        12 * (m + n + remAll) + 21 * (L + 1) + 25 * w + 50
    have hP1 : (L + remAll * (L + 1)) * (19 * w + 20) + 12 * remAll + 7 * L + 25 * w + 37 ≤ P := by
      have h1 : (L + remAll * (L + 1)) * (19 * w + 20) ≤
          (L + 1 + (m + n + remAll) * (L + 1)) * (19 * w + 20) :=
        Nat.mul_le_mul_right _ (Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ (by omega)))
      omega
    have hP2 : (L + m * (L + 1) + n * (L + 1)) * (19 * w + 20) + 12 * m + 7 * n + 21 * L + 25 * w + 46 ≤ P := by
      have h1 : (L + m * (L + 1) + n * (L + 1)) * (19 * w + 20) ≤
          (L + 1 + (m + n + remAll) * (L + 1)) * (19 * w + 20) := by
        refine Nat.mul_le_mul_right _ ?_
        have hmn : m * (L + 1) + n * (L + 1) = (m + n) * (L + 1) := by ring
        have hle : (m + n) * (L + 1) ≤ (m + n + remAll) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      omega
    have hmul : (L + 1) * P = L * P + P := by ring
    have hLP : L * ((L + remAll * (L + 1)) * (19 * w + 20) + 12 * remAll + 7 * L + 25 * w + 37) ≤ L * P :=
      Nat.mul_le_mul_left L hP1
    omega

theorem rightBlock_spec (S : WK → List Bool) (w x L remAll : ℕ)
    (hL1 : (S wL1).length = L + 1) (hRA : (S wRemAll).length = remAll + 1)
    (hX : S wX = fieldBits w x) (hY : S wY = []) (hRR : S wRemR = [])
    (hC : S wCnt = []) (hB : S wBlk = []) (hRx : S wRxLoop = []) (ht1 : S wTmp1 = []) :
    rightBlockExec S =
      Function.update (Function.update (Function.update S
        wRemAll (S wRemAll).tail)
        wOutRev ((emitNoBaseLoop w x remAll (L + 1) (L + 1)).reverse ++ S wOutRev))
        wX (fieldBits w (x + L + 1)) ∧
    rightBlockCost S ≤
      (L + 1) * (((L + 1) + remAll * (L + 1)) * (19 * w + 20) +
        12 * remAll + 7 * (L + 1) + 25 * w + 37) + 14 * (L + 1) + 10 := by
  let S1 := Function.update S wRemAll (S wRemAll).tail
  have hS1RA : (S1 wRemAll).length = remAll := by simp [S1, hRA]
  have hS2 : copyExec wL1 wRemR wTmp1 S1 = Function.update S1 wRemR (S wL1) := by
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S1 (by simp [S1, Fin.ext_iff, ht1])]
    simp [S1, Fin.ext_iff, hRR]
  have hS3 : copyExec wL1 wRxLoop wTmp1 (copyExec wL1 wRemR wTmp1 S1) =
      Function.update (Function.update S1 wRemR (S wL1)) wRxLoop (S wL1) := by
    rw [hS2, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [S1, Fin.ext_iff, ht1])]
    simp [S1, Fin.ext_iff, hRx]
  have hNB := noBaseLoop_spec (copyExec wL1 wRxLoop wTmp1 (copyExec wL1 wRemR wTmp1 S1)) w x
    (by rw [hS3]; simp [Fin.ext_iff]) (by rw [hS3]; simp [S1, Fin.ext_iff, hX])
    (by rw [hS3]; simp [S1, Fin.ext_iff, hY]) (by rw [hS3]; simp [S1, Fin.ext_iff, hC])
    (by rw [hS3]; simp [S1, Fin.ext_iff, hB]) (by rw [hS3]; simp [S1, Fin.ext_iff, ht1])
  refine ⟨?_, ?_⟩
  · simp only [rightBlockExec]
    change noBaseLoopExec (copyExec wL1 wRxLoop wTmp1 (copyExec wL1 wRemR wTmp1 S1)) = _
    rw [hNB.1, hS3]
    funext j
    by_cases j1 : j = wX
    · subst j1; simp [Fin.ext_iff, hL1, show x + (L + 1) = x + L + 1 by omega]
    by_cases j2 : j = wOutRev
    · subst j2; simp [S1, Fin.ext_iff, hL1, hRA]
    by_cases j3 : j = wRemR; · subst j3; simp [S1, Fin.ext_iff, hRR]
    by_cases j4 : j = wRxLoop; · subst j4; simp [S1, Fin.ext_iff, hRx]
    by_cases j5 : j = wRemAll; · subst j5; simp [S1, Fin.ext_iff]
    simp [S1, Fin.ext_iff, j1, j2, j3, j4, j5]
  · simp only [rightBlockCost]
    change noBaseLoopCost (copyExec wL1 wRxLoop wTmp1 (copyExec wL1 wRemR wTmp1 S1)) +
      ((7 * (copyExec wL1 wRemR wTmp1 S1 wL1).length + 4 * (copyExec wL1 wRemR wTmp1 S1 wTmp1).length + 2) +
       ((7 * (S1 wL1).length + 4 * (S1 wTmp1).length + 2) + 1)) ≤ _
    have hc := hNB.2
    have hS3Rx : (copyExec wL1 wRxLoop wTmp1 (copyExec wL1 wRemR wTmp1 S1) wRxLoop).length = L + 1 := by
      rw [hS3]; simp [hL1]
    have hS3RA : (copyExec wL1 wRxLoop wTmp1 (copyExec wL1 wRemR wTmp1 S1) wRemAll).length = remAll := by
      rw [hS3]; simp [Fin.ext_iff, hS1RA]
    have hS3L1 : (copyExec wL1 wRxLoop wTmp1 (copyExec wL1 wRemR wTmp1 S1) wL1).length = L + 1 := by
      rw [hS3]; simp [S1, Fin.ext_iff, hL1]
    rw [hS3Rx, hS3RA, hS3L1] at hc
    have hS2L1 : (copyExec wL1 wRemR wTmp1 S1 wL1).length = L + 1 := by rw [hS2]; simp [S1, Fin.ext_iff, hL1]
    have hS2t : (copyExec wL1 wRemR wTmp1 S1 wTmp1).length = 0 := by rw [hS2]; simp [S1, Fin.ext_iff, ht1]
    have hS1L1 : (S1 wL1).length = L + 1 := by simp [S1, Fin.ext_iff, hL1]
    have hS1t : (S1 wTmp1).length = 0 := by simp [S1, Fin.ext_iff, ht1]
    rw [hS2L1, hS2t, hS1L1, hS1t]
    omega


def dup2VStepExec (S : WK → List Bool) : WK → List Bool :=
  Function.update S wV (true :: true :: S wV)

theorem psb_dup2VStep : PureSB dup2VStepExec (fun _ => 2) := by
  refine psb_congr (psb_seq (psb_push wV true) (psb_push wV true)) ?_
  intro S; funext j; by_cases hj : j = wV; · subst hj; simp [dup2VStepExec]
  simp [dup2VStepExec, hj]

theorem indep_dup2VStep : Indep wTmp2 dup2VStepExec := by
  intro S l; funext j; simp only [dup2VStepExec]
  by_cases j1 : j = wTmp2; · subst j1; simp [Fin.ext_iff]
  by_cases j2 : j = wV; · subst j2; simp [Fin.ext_iff]
  simp [Fin.ext_iff, j1, j2]

def copyT2WExec (S : WK → List Bool) : WK → List Bool :=
  copyExec wT wL wTmp1 (copyExec wT wL wTmp1 S)

def copyT2WCost (S : WK → List Bool) : ℕ :=
  (7 * (copyExec wT wL wTmp1 S wT).length + 4 * (copyExec wT wL wTmp1 S wTmp1).length + 2) +
    (7 * (S wT).length + 4 * (S wTmp1).length + 2)

theorem psb_copyT2W : PureSB copyT2WExec copyT2WCost := by
  unfold copyT2WExec copyT2WCost
  exact psb_seq (psb_copy (a := wT) (b := wL) (tmp := wTmp1) (by decide) (by decide) (by decide))
                (psb_copy (a := wT) (b := wL) (tmp := wTmp1) (by decide) (by decide) (by decide))

theorem indep_copyT2W : Indep wTmp2 copyT2WExec := by
  unfold copyT2WExec
  exact indep_seq (indep_copy (a := wT) (b := wL) (tmp := wTmp1) (by decide) (by decide) (by decide))
                  (indep_copy (a := wT) (b := wL) (tmp := wTmp1) (by decide) (by decide) (by decide))

def kHdrStepExec (S : WK → List Bool) : WK → List Bool :=
  incBinExec wT wTmp1 (Function.update S wOutRev (true :: S wOutRev))

def kHdrStepCost (S : WK → List Bool) : ℕ :=
  (5 * (Function.update S wOutRev (true :: S wOutRev) wT).length +
   3 * (Function.update S wOutRev (true :: S wOutRev) wTmp1).length + 7) + 1

theorem psb_kHdrStep : PureSB kHdrStepExec kHdrStepCost := by
  unfold kHdrStepExec kHdrStepCost
  exact psb_seq (psb_push wOutRev true) (psb_incBin (x := wT) (tmp := wTmp1) (by decide))

theorem indep_kHdrStep : Indep wBlk kHdrStepExec := by
  unfold kHdrStepExec
  exact indep_seq (indep_push (k' := wOutRev) (by decide) true) (indep_incBin (x := wT) (tmp := wTmp1) (by decide) (by decide))

def wStageAExec (S : WK → List Bool) : WK → List Bool :=
  let S1 := parseHeaderExec wIn wN S
  let S2 := copyExec wN wTmp2 wTmp1 S1
  let S3 := (S2 wTmp2).foldl (fun U _ => dup2VStepExec U) (Function.update S2 wTmp2 [])
  let S4 := incBinExec wT wTmp1 S3
  let S5 := copyExec wV wTmp2 wTmp1 S4
  (S5 wTmp2).foldl (fun U _ => incBinExec wT wTmp1 U) (Function.update S5 wTmp2 [])

def wStageACost (S : WK → List Bool) : ℕ :=
  let S1 := parseHeaderExec wIn wN S
  let S2 := copyExec wN wTmp2 wTmp1 S1
  let S3 := (S2 wTmp2).foldl (fun U _ => dup2VStepExec U) (Function.update S2 wTmp2 [])
  let S4 := incBinExec wT wTmp1 S3
  let S5 := copyExec wV wTmp2 wTmp1 S4
  forEachCost wTmp2 (fun _ => incBinExec wT wTmp1)
    (fun _ U => 5 * (U wT).length + 3 * (U wTmp1).length + 7) (S5 wTmp2) S5 +
    ((7 * (S4 wV).length + 4 * (S4 wTmp1).length + 2) +
      ((5 * (S3 wT).length + 3 * (S3 wTmp1).length + 7) +
        (forEachCost wTmp2 (fun _ => dup2VStepExec) (fun _ _ => 2) (S2 wTmp2) S2 +
          ((7 * (S1 wN).length + 4 * (S1 wTmp1).length + 2) + (2 * (S wIn).length + 3)))))

theorem psb_wStageA : PureSB wStageAExec wStageACost := by
  unfold wStageAExec wStageACost
  exact psb_seq
    (psb_seq
      (psb_seq
        (psb_seq
          (psb_seq (psb_parseHeader (inp := wIn) (N := wN) (by decide))
            (psb_copy (a := wN) (b := wTmp2) (tmp := wTmp1) (by decide) (by decide) (by decide)))
          (psb_forEachIgn wTmp2 psb_dup2VStep indep_dup2VStep))
        (psb_incBin (x := wT) (tmp := wTmp1) (by decide)))
      (psb_copy (a := wV) (b := wTmp2) (tmp := wTmp1) (by decide) (by decide) (by decide)))
    (psb_forEachIgn wTmp2 (psb_incBin (x := wT) (tmp := wTmp1) (by decide))
      (indep_incBin (x := wT) (tmp := wTmp1) (by decide) (by decide)))

def wStageBExec (S : WK → List Bool) : WK → List Bool :=
  let S1 := Function.update S wL (true :: true :: S wL)
  let S2 := copyExec wV wTmp2 wTmp1 S1
  let S3 := (S2 wTmp2).foldl (fun U _ => copyT2WExec U) (Function.update S2 wTmp2 [])
  let S4 := clearExec wT S3
  let S5 := copyExec wL wL1 wTmp1 S4
  let S6 := Function.update S5 wL1 (true :: S5 wL1)
  let S7 := copyExec wL wLm1 wTmp1 S6
  Function.update S7 wLm1 (S7 wLm1).tail

def wStageBCost (S : WK → List Bool) : ℕ :=
  let S1 := Function.update S wL (true :: true :: S wL)
  let S2 := copyExec wV wTmp2 wTmp1 S1
  let S3 := (S2 wTmp2).foldl (fun U _ => copyT2WExec U) (Function.update S2 wTmp2 [])
  let S4 := clearExec wT S3
  let S5 := copyExec wL wL1 wTmp1 S4
  let S6 := Function.update S5 wL1 (true :: S5 wL1)
  1 + ((7 * (S6 wL).length + 4 * (S6 wTmp1).length + 2) +
    (1 + ((7 * (S4 wL).length + 4 * (S4 wTmp1).length + 2) +
      ((3 * (S3 wT).length + 1) +
        (forEachCost wTmp2 (fun _ => copyT2WExec) (fun _ => copyT2WCost) (S2 wTmp2) S2 +
          ((7 * (S1 wV).length + 4 * (S1 wTmp1).length + 2) + 2))))))

theorem psb_wStageB : PureSB wStageBExec wStageBCost := by
  unfold wStageBExec wStageBCost
  have hp2 : PureSB (fun S : WK → List Bool => Function.update S wL (true :: true :: S wL)) (fun _ => 2) := by
    refine psb_congr (psb_seq (psb_push wL true) (psb_push wL true)) ?_
    intro S; funext j; by_cases hj : j = wL; · subst hj; simp
    simp [hj]
  exact psb_seq
    (psb_seq
      (psb_seq
        (psb_seq
          (psb_seq
            (psb_seq
              (psb_seq hp2 (psb_copy (a := wV) (b := wTmp2) (tmp := wTmp1) (by decide) (by decide) (by decide)))
              (psb_forEachIgn wTmp2 psb_copyT2W indep_copyT2W))
            (psb_clear wT))
          (psb_copy (a := wL) (b := wL1) (tmp := wTmp1) (by decide) (by decide) (by decide)))
        (psb_push wL1 true))
      (psb_copy (a := wL) (b := wLm1) (tmp := wTmp1) (by decide) (by decide) (by decide)))
    (psb_popDrop wLm1)

def wStageCExec (S : WK → List Bool) : WK → List Bool :=
  let S1 := copyExec wV wTmp2 wTmp1 S
  let S2 := (S1 wTmp2).foldl (fun U _ => copyExec wL1 wBlk wTmp1 U) (Function.update S1 wTmp2 [])
  let S3 := (S2 wBlk).foldl (fun U _ => kHdrStepExec U) (Function.update S2 wBlk [])
  let S4 := Function.update S3 wOutRev (false :: S3 wOutRev)
  let S5 := (S4 wT).foldl (fun U _ => Function.update U wX (false :: U wX)) (Function.update S4 wT [])
  let S6 := copyExec wN wRemLeft wTmp1 S5
  let S7 := copyExec wV wRemAll wTmp1 S6
  clearExec wV S7

def wStageCCost (S : WK → List Bool) : ℕ :=
  let S1 := copyExec wV wTmp2 wTmp1 S
  let S2 := (S1 wTmp2).foldl (fun U _ => copyExec wL1 wBlk wTmp1 U) (Function.update S1 wTmp2 [])
  let S3 := (S2 wBlk).foldl (fun U _ => kHdrStepExec U) (Function.update S2 wBlk [])
  let S4 := Function.update S3 wOutRev (false :: S3 wOutRev)
  let S5 := (S4 wT).foldl (fun U _ => Function.update U wX (false :: U wX)) (Function.update S4 wT [])
  let S6 := copyExec wN wRemLeft wTmp1 S5
  let S7 := copyExec wV wRemAll wTmp1 S6
  (3 * (S7 wV).length + 1) +
    ((7 * (S6 wV).length + 4 * (S6 wTmp1).length + 2) +
      ((7 * (S5 wN).length + 4 * (S5 wTmp1).length + 2) +
        (forEachCost wT (fun _ U => Function.update U wX (false :: U wX)) (fun _ _ => 1) (S4 wT) S4 +
          (1 + (forEachCost wBlk (fun _ => kHdrStepExec) (fun _ => kHdrStepCost) (S2 wBlk) S2 +
            (forEachCost wTmp2 (fun _ => copyExec wL1 wBlk wTmp1)
              (fun _ U => 7 * (U wL1).length + 4 * (U wTmp1).length + 2) (S1 wTmp2) S1 +
              (7 * (S wV).length + 4 * (S wTmp1).length + 2)))))))

theorem psb_wStageC : PureSB wStageCExec wStageCCost := by
  unfold wStageCExec wStageCCost
  exact psb_seq
    (psb_seq
      (psb_seq
        (psb_seq
          (psb_seq
            (psb_seq
              (psb_seq (psb_copy (a := wV) (b := wTmp2) (tmp := wTmp1) (by decide) (by decide) (by decide))
                (psb_forEachIgn wTmp2 (psb_copy (a := wL1) (b := wBlk) (tmp := wTmp1) (by decide) (by decide) (by decide))
                  (indep_copy (a := wL1) (b := wBlk) (tmp := wTmp1) (by decide) (by decide) (by decide))))
              (psb_forEachIgn wBlk psb_kHdrStep indep_kHdrStep))
            (psb_push wOutRev false))
          (psb_forEachIgn wT (psb_push wX false) (indep_push (k' := wX) (by decide) false)))
        (psb_copy (a := wN) (b := wRemLeft) (tmp := wTmp1) (by decide) (by decide) (by decide)))
      (psb_copy (a := wV) (b := wRemAll) (tmp := wTmp1) (by decide) (by decide) (by decide)))
    (psb_clear wV)

def wStageDExec (S : WK → List Bool) : WK → List Bool :=
  let S1 := copyExec wN wNloop wTmp1 S
  let S2 := (S1 wNloop).foldl (fun U _ => leftBlockExec U) (Function.update S1 wNloop [])
  let S3 := copyExec wN wNloop wTmp1 S2
  let S4 := (S3 wNloop).foldl (fun U _ => rightBlockExec U) (Function.update S3 wNloop [])
  let S5 := clearExec wIn S4
  let S6 := clearExec wN S5
  let S7 := clearExec wL S6
  let S8 := clearExec wL1 S7
  let S9 := clearExec wLm1 S8
  let S10 := clearExec wX S9
  revMoveExec wOutRev wOut S10

def wStageDCost (S : WK → List Bool) : ℕ :=
  let S1 := copyExec wN wNloop wTmp1 S
  let S2 := (S1 wNloop).foldl (fun U _ => leftBlockExec U) (Function.update S1 wNloop [])
  let S3 := copyExec wN wNloop wTmp1 S2
  let S4 := (S3 wNloop).foldl (fun U _ => rightBlockExec U) (Function.update S3 wNloop [])
  let S5 := clearExec wIn S4
  let S6 := clearExec wN S5
  let S7 := clearExec wL S6
  let S8 := clearExec wL1 S7
  let S9 := clearExec wLm1 S8
  let S10 := clearExec wX S9
  (3 * (S10 wOutRev).length + 1) +
    ((3 * (S9 wX).length + 1) +
      ((3 * (S8 wLm1).length + 1) +
        ((3 * (S7 wL1).length + 1) +
          ((3 * (S6 wL).length + 1) +
            ((3 * (S5 wN).length + 1) +
              ((3 * (S4 wIn).length + 1) +
                (forEachCost wNloop (fun _ => rightBlockExec) (fun _ => rightBlockCost) (S3 wNloop) S3 +
                  ((7 * (S2 wN).length + 4 * (S2 wTmp1).length + 2) +
                    (forEachCost wNloop (fun _ => leftBlockExec) (fun _ => leftBlockCost) (S1 wNloop) S1 +
                      (7 * (S wN).length + 4 * (S wTmp1).length + 2))))))))))

theorem psb_wStageD : PureSB wStageDExec wStageDCost := by
  unfold wStageDExec wStageDCost
  exact psb_seq
    (psb_seq
      (psb_seq
        (psb_seq
          (psb_seq
            (psb_seq
              (psb_seq
                (psb_seq
                  (psb_seq
                    (psb_seq (psb_copy (a := wN) (b := wNloop) (tmp := wTmp1) (by decide) (by decide) (by decide))
                      (psb_forEachIgn wNloop psb_leftBlock indep_leftBlock))
                    (psb_copy (a := wN) (b := wNloop) (tmp := wTmp1) (by decide) (by decide) (by decide)))
                  (psb_forEachIgn wNloop psb_rightBlock indep_rightBlock))
                (psb_clear wIn))
              (psb_clear wN))
            (psb_clear wL))
          (psb_clear wL1))
        (psb_clear wLm1))
      (psb_clear wX))
    (psb_revMove (a := wOutRev) (b := wOut) (by decide))

def writeExec (S : WK → List Bool) : WK → List Bool :=
  wStageDExec (wStageCExec (wStageBExec (wStageAExec S)))

def writeCost (S : WK → List Bool) : ℕ :=
  let S1 := wStageAExec S
  let S2 := wStageBExec S1
  let S3 := wStageCExec S2
  wStageDCost S3 + (wStageCCost S2 + (wStageBCost S1 + wStageACost S))

theorem psb_write : PureSB writeExec writeCost := by
  unfold writeExec writeCost
  exact psb_seq (psb_seq (psb_seq psb_wStageA psb_wStageB) psb_wStageC) psb_wStageD


theorem emitRange_len (w x y m : ℕ) : (emitRange w x y m).length = m * (2 * w) := by
  induction m generalizing y with
  | zero => simp [emitRange]
  | succ m ih =>
    rw [emitRange_succ_front, List.length_append, ih, emitPairBits, List.length_append,
        fieldBits_length, fieldBits_length]
    ring

theorem emitNoBase_len_le (w x remR remAll L1 : ℕ) :
    (emitNoBase w x remR remAll L1).length ≤ (remR + remAll * L1) * (2 * w) := by
  simp only [emitNoBase, List.length_append, emitRange_len]
  split
  · simp only [List.length_nil, Nat.zero_add]; exact Nat.mul_le_mul_right _ (by omega)
  · rw [emitRange_len]
    have h1 : (remR - 1) * (2 * w) + remAll * L1 * (2 * w) = (remR - 1 + remAll * L1) * (2 * w) := by ring
    rw [h1]; exact Nat.mul_le_mul_right _ (by omega)

theorem emitRow_len_le (w x y L : ℕ) : ∀ row : List Bool,
    (emitRow w x y L row).length ≤ row.length * (L + 1) * (2 * w)
  | [] => by simp [emitRow]
  | b :: bs => by
    have ih := emitRow_len_le w x (y + (L + 1)) L bs
    simp only [emitRow, List.length_append, emitRange_len, List.length_cons]
    have hb : (if b then ([] : List Bool) else emitPairBits w x y).length ≤ 2 * w := by
      cases b <;> simp [emitPairBits, fieldBits_length]; omega
    have h1 : (bs.length + 1) * (L + 1) * (2 * w) =
        2 * w + L * (2 * w) + bs.length * (L + 1) * (2 * w) := by ring
    omega

theorem emitLeftRx0_len_le (w x L remLeft : ℕ) (row : List Bool) :
    (emitLeftRx0 w x L remLeft row).length ≤
      (L + remLeft * (L + 1) + row.length * (L + 1)) * (2 * w) := by
  simp only [emitLeftRx0, List.length_append, emitRange_len]
  have hr := emitRow_len_le w x (x + L + 1 + remLeft * (L + 1)) L row
  have h1 : (L - 1) * (2 * w) ≤ L * (2 * w) := Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  have h2 : (L + remLeft * (L + 1) + row.length * (L + 1)) * (2 * w) =
      L * (2 * w) + remLeft * (L + 1) * (2 * w) + row.length * (L + 1) * (2 * w) := by ring
  omega

theorem emitNoBaseLoop_len_le (w x remAll L1 : ℕ) : ∀ r : ℕ,
    (emitNoBaseLoop w x remAll L1 r).length ≤ r * (r + remAll * L1) * (2 * w)
  | 0 => by simp [emitNoBaseLoop]
  | r + 1 => by
    have ih := emitNoBaseLoop_len_le w (x + 1) remAll L1 r
    have h0 := emitNoBase_len_le w x r remAll L1
    simp only [emitNoBaseLoop, List.length_append]
    have h1 : r * (r + remAll * L1) * (2 * w) ≤ r * (r + 1 + remAll * L1) * (2 * w) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    have h2 : (r + remAll * L1) * (2 * w) ≤ (r + 1 + remAll * L1) * (2 * w) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : (r + 1) * (r + 1 + remAll * L1) * (2 * w) =
        (r + 1 + remAll * L1) * (2 * w) + r * (r + 1 + remAll * L1) * (2 * w) := by ring
    omega

theorem emitLeftBlocks_len_le (w L n : ℕ) : ∀ (m x remAll : ℕ) (a : List Bool),
    (emitLeftBlocks w L n m x remAll a).length ≤
      m * (L + 1) * (L + 1 + (m + n + remAll) * (L + 1)) * (2 * w)
  | 0, _, _, _ => by simp [emitLeftBlocks]
  | m + 1, x, remAll, a => by
    have ih := emitLeftBlocks_len_le w L n m (x + L + 1) (remAll - 1) (a.drop n)
    have h0 := emitLeftRx0_len_le w x L m ((List.range n).map (fun i => a.getD i false))
    simp only [List.length_map, List.length_range] at h0
    have h1 := emitNoBaseLoop_len_le w (x + 1) (remAll - 1) (L + 1) L
    simp only [emitLeftBlocks, List.length_append]
    set B := L + 1 + (m + 1 + n + remAll) * (L + 1)
    have hB0 : (L + m * (L + 1) + n * (L + 1)) * (2 * w) ≤ B * (2 * w) := by
      refine Nat.mul_le_mul_right _ ?_
      have hmn : m * (L + 1) + n * (L + 1) = (m + n) * (L + 1) := by ring
      have hle : (m + n) * (L + 1) ≤ (m + 1 + n + remAll) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
      simp only [B]; omega
    have hB1 : L * (L + (remAll - 1) * (L + 1)) * (2 * w) ≤ L * B * (2 * w) := by
      refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left L ?_)
      have hle : (remAll - 1) * (L + 1) ≤ (m + 1 + n + remAll) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
      simp only [B]; omega
    have hB2 : m * (L + 1) * (L + 1 + (m + n + (remAll - 1)) * (L + 1)) * (2 * w) ≤
        m * (L + 1) * B * (2 * w) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by
        have : (m + n + (remAll - 1)) * (L + 1) ≤ (m + 1 + n + remAll) * (L + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega))
    have h3 : (m + 1) * (L + 1) * B * (2 * w) =
        B * (2 * w) + L * B * (2 * w) + m * (L + 1) * B * (2 * w) := by ring
    omega

theorem emitRightBlocks_len_le (w L : ℕ) : ∀ (m x remAll : ℕ),
    (emitRightBlocks w L m x remAll).length ≤
      m * (L + 1) * (L + 1 + remAll * (L + 1)) * (2 * w)
  | 0, _, _ => by simp [emitRightBlocks]
  | m + 1, x, remAll => by
    have ih := emitRightBlocks_len_le w L m (x + L + 1) (remAll - 1)
    have h0 := emitNoBaseLoop_len_le w x (remAll - 1) (L + 1) (L + 1)
    simp only [emitRightBlocks, List.length_append]
    set B := L + 1 + remAll * (L + 1)
    have hB0 : (L + 1) * (L + 1 + (remAll - 1) * (L + 1)) * (2 * w) ≤ (L + 1) * B * (2 * w) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by
        have : (remAll - 1) * (L + 1) ≤ remAll * (L + 1) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        omega))
    have hB1 : m * (L + 1) * (L + 1 + (remAll - 1) * (L + 1)) * (2 * w) ≤
        m * (L + 1) * B * (2 * w) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by
        have : (remAll - 1) * (L + 1) ≤ remAll * (L + 1) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        omega))
    have h3 : (m + 1) * (L + 1) * B * (2 * w) =
        (L + 1) * B * (2 * w) + m * (L + 1) * B * (2 * w) := by ring
    omega

theorem wStageA_spec (inp : List Bool) :
    let S0 := Function.update (fun _ : WK => ([] : List Bool)) wIn inp
    let n := (inp.takeWhile id).length
    let a := (inp.dropWhile id).tail
    let v := 2 * n
    wStageAExec S0 =
      Function.update (Function.update (Function.update (Function.update S0 wIn a)
        wN (List.replicate n true)) wV (List.replicate v true)) wT (v + 1).bits ∧
    wStageACost S0 ≤ 5 * (v + 1) ^ 2 + 30 * (v + 1) + 2 * inp.length + 30 := by
  intro S0 n a v
  have hS1 : parseHeaderExec wIn wN S0 =
      Function.update (Function.update S0 wIn a) wN (List.replicate n true) := by
    rw [parseHeaderExec_eq (by decide)]
    funext j
    by_cases j1 : j = wN; · subst j1; simp [S0, Fin.ext_iff, n]
    by_cases j2 : j = wIn; · subst j2; simp [S0, Fin.ext_iff, a]
    simp [S0, Fin.ext_iff, j1, j2]
  have hS2 : copyExec wN wTmp2 wTmp1 (parseHeaderExec wIn wN S0) =
      Function.update (Function.update (Function.update S0 wIn a) wN (List.replicate n true))
        wTmp2 (List.replicate n true) := by
    rw [hS1, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [S0, Fin.ext_iff])]
    simp [S0, Fin.ext_iff]
  have hdup : ∀ (l : List Bool) (U : WK → List Bool),
      l.foldl (fun W _ => dup2VStepExec W) U =
        Function.update U wV (List.replicate (2 * l.length) true ++ U wV) := by
    intro l
    induction l with
    | nil => intro U; simp [Function.update_eq_self]
    | cons _ l ih =>
      intro U
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      funext j
      by_cases j1 : j = wV
      · subst j1
        simp only [dup2VStepExec, Function.update_self]
        rw [show 2 * (l.length + 1) = 2 * l.length + 2 by omega, List.replicate_add]
        simp [List.append_assoc, replicate_append_cons]
      · simp [dup2VStepExec, j1]
  have hS3 : ((copyExec wN wTmp2 wTmp1 (parseHeaderExec wIn wN S0)) wTmp2).foldl
      (fun U _ => dup2VStepExec U)
      (Function.update (copyExec wN wTmp2 wTmp1 (parseHeaderExec wIn wN S0)) wTmp2 []) =
      Function.update (Function.update (Function.update S0 wIn a) wN (List.replicate n true))
        wV (List.replicate v true) := by
    rw [hS2]; simp only [Function.update_self]
    rw [hdup]
    funext j
    by_cases j1 : j = wV; · subst j1; simp [S0, Fin.ext_iff, v]
    by_cases j2 : j = wTmp2; · subst j2; simp [S0, Fin.ext_iff]
    by_cases j3 : j = wN; · subst j3; simp [S0, Fin.ext_iff]
    by_cases j4 : j = wIn; · subst j4; simp [S0, Fin.ext_iff]
    simp [S0, Fin.ext_iff, j1, j2, j3, j4]
  have hS4 : incBinExec wT wTmp1 (((copyExec wN wTmp2 wTmp1 (parseHeaderExec wIn wN S0)) wTmp2).foldl
      (fun U _ => dup2VStepExec U)
      (Function.update (copyExec wN wTmp2 wTmp1 (parseHeaderExec wIn wN S0)) wTmp2 [])) =
      Function.update (Function.update (Function.update (Function.update S0 wIn a) wN (List.replicate n true))
        wV (List.replicate v true)) wT [true] := by
    rw [hS3, incBinExec_of_empty (by decide) _ (by simp [S0, Fin.ext_iff])]
    simp [S0, Fin.ext_iff, incBits]
  have hS5 : copyExec wV wTmp2 wTmp1 (incBinExec wT wTmp1
      (((copyExec wN wTmp2 wTmp1 (parseHeaderExec wIn wN S0)) wTmp2).foldl
        (fun U _ => dup2VStepExec U)
        (Function.update (copyExec wN wTmp2 wTmp1 (parseHeaderExec wIn wN S0)) wTmp2 []))) =
      Function.update (Function.update (Function.update (Function.update (Function.update S0 wIn a)
        wN (List.replicate n true)) wV (List.replicate v true)) wT [true]) wTmp2 (List.replicate v true) := by
    rw [hS4, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [S0, Fin.ext_iff])]
    simp [S0, Fin.ext_iff]
  have hfold : ∀ (l : List Bool) (m : ℕ) (U : WK → List Bool),
      U wT = m.bits → U wTmp1 = [] →
      l.foldl (fun W _ => incBinExec wT wTmp1 W) U = Function.update U wT (m + l.length).bits ∧
      forEachCost wTmp2 (fun _ => incBinExec wT wTmp1)
        (fun _ W => 5 * (W wT).length + 3 * (W wTmp1).length + 7) l U ≤
        l.length * (5 * (m + l.length) + 9) + 1 := by
    intro l
    induction l with
    | nil =>
      intro m U hUT _
      exact ⟨by simp [hUT, Function.update_eq_self], by simp [forEachCost]⟩
    | cons _ l ih =>
      intro m U hUT hU1
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have hi1 : incBinExec wT wTmp1 U = Function.update U wT (m + 1).bits := by
        rw [incBinExec_of_empty (by decide) U hU1, hUT, incBits_bits]
      have hi2 : incBinExec wT wTmp1 (Function.update U wTmp2 l) =
          Function.update (Function.update U wTmp2 l) wT (m + 1).bits := by
        rw [incBinExec_of_empty (by decide) _ (by simp [Fin.ext_iff, hU1]),
            Function.update_of_ne (by decide), hUT, incBits_bits]
      have hr1 := ih (m + 1) (incBinExec wT wTmp1 U) (by rw [hi1]; simp) (by rw [hi1]; simp [Fin.ext_iff, hU1])
      have hr2 := ih (m + 1) (incBinExec wT wTmp1 (Function.update U wTmp2 l))
        (by rw [hi2]; simp) (by rw [hi2]; simp [Fin.ext_iff, hU1])
      refine ⟨?_, ?_⟩
      · rw [hr1.1, hi1, Function.update_idem, show m + 1 + l.length = m + (l.length + 1) by omega]
      · have hlen : (Function.update U wTmp2 l wT).length ≤ m := by
          rw [Function.update_of_ne (by decide), hUT]; exact bits_length_le m
        have hu1' : (Function.update U wTmp2 l wTmp1).length = 0 := by
          rw [Function.update_of_ne (by decide), hU1]; rfl
        have hc2 := hr2.2
        rw [show m + 1 + l.length = m + (l.length + 1) by omega] at hc2
        have hmul : (l.length + 1) * (5 * (m + (l.length + 1)) + 9) =
            l.length * (5 * (m + (l.length + 1)) + 9) + (5 * (m + (l.length + 1)) + 9) := by ring
        omega
  have hr1 := hfold (List.replicate v true) 1
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update S0 wIn a)
      wN (List.replicate n true)) wV (List.replicate v true)) wT [true]) wTmp2 (List.replicate v true)) wTmp2 [])
    (by simp [Fin.ext_iff]) (by simp [S0, Fin.ext_iff])
  have hr2 := hfold (List.replicate v true) 1
    (Function.update (Function.update (Function.update (Function.update (Function.update S0 wIn a)
      wN (List.replicate n true)) wV (List.replicate v true)) wT [true]) wTmp2 (List.replicate v true))
    (by simp [Fin.ext_iff]) (by simp [S0, Fin.ext_iff])
  refine ⟨?_, ?_⟩
  · simp only [wStageAExec]
    rw [hS5]; simp only [Function.update_self]; rw [hr1.1]
    funext j
    by_cases j1 : j = wT; · subst j1; simp [Fin.ext_iff, Nat.add_comm]
    by_cases j2 : j = wTmp2; · subst j2; simp [S0, Fin.ext_iff]
    by_cases j3 : j = wV; · subst j3; simp [Fin.ext_iff]
    by_cases j4 : j = wN; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = wIn; · subst j5; simp [Fin.ext_iff]
    simp [S0, Fin.ext_iff, j1, j2, j3, j4, j5]
  · simp only [wStageACost]
    rw [hS5, hS4, hS3, hS2, hS1]
    have hcdup := forEachCost_le wTmp2 (fun _ => dup2VStepExec) (fun _ _ => 2) (fun _ => True) 2
      (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial)
      (List.replicate n true)
      (Function.update (Function.update (Function.update S0 wIn a) wN (List.replicate n true)) wTmp2 (List.replicate n true))
      trivial
    have hct := hr2.2
    simp only [Function.update_self, Function.update_of_ne (by decide : wV ≠ wT),
      Function.update_of_ne (by decide : wTmp1 ≠ wT), Function.update_of_ne (by decide : wTmp1 ≠ wV),
      Function.update_of_ne (by decide : wTmp1 ≠ wN), Function.update_of_ne (by decide : wTmp1 ≠ wIn),
      Function.update_of_ne (by decide : wT ≠ wV), Function.update_of_ne (by decide : wT ≠ wN),
      Function.update_of_ne (by decide : wT ≠ wIn), S0, List.length_replicate, List.length_nil] at hcdup hct ⊢
    have hv2n : v = 2 * n := rfl
    have hle1 : v * (5 * (1 + v) + 9) ≤ (v + 1) * (5 * (v + 1) + 9) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hle2 : (v + 1) * (5 * (v + 1) + 9) = 5 * (v + 1) ^ 2 + 9 * (v + 1) := by ring
    omega

theorem wStageB_spec (S : WK → List Bool) (v t : ℕ)
    (hV : (S wV).length = v) (hT : (S wT).length = t)
    (hL : S wL = []) (hL1 : S wL1 = []) (hLm1 : S wLm1 = [])
    (ht1 : S wTmp1 = []) (ht2 : S wTmp2 = []) :
    let L := 2 * (1 + v * t)
    ∃ (lL lL1 lLm1 : List Bool),
      lL.length = L ∧ lL1.length = L + 1 ∧ lLm1.length = L - 1 ∧
      wStageBExec S =
        Function.update (Function.update (Function.update (Function.update S wT [])
          wL lL) wL1 lL1) wLm1 lLm1 ∧
      wStageBCost S ≤ 16 * v * t + 14 * L + 14 * v + 3 * t + 20 := by
  intro L
  have hcopy2 : ∀ (U : WK → List Bool), U wTmp1 = [] →
      copyT2WExec U = Function.update U wL (U wT ++ U wT ++ U wL) ∧
      copyT2WCost U ≤ 14 * (U wT).length + 4 := by
    intro U hU1
    have hc1 : copyExec wT wL wTmp1 U = Function.update U wL (U wT ++ U wL) :=
      copyExec_of_empty (by decide) (by decide) (by decide) U hU1
    have hc2 : copyExec wT wL wTmp1 (copyExec wT wL wTmp1 U) =
        Function.update U wL (U wT ++ U wT ++ U wL) := by
      rw [hc1, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, hU1])]
      funext j; by_cases hj : j = wL; · subst hj; simp [Fin.ext_iff, List.append_assoc]
      simp [Fin.ext_iff, hj]
    refine ⟨hc2, ?_⟩
    simp only [copyT2WCost, hc1, Function.update_of_ne (by decide : wT ≠ wL),
      Function.update_of_ne (by decide : wTmp1 ≠ wL), hU1, List.length_nil]
    omega
  have hfold : ∀ (l : List Bool) (U : WK → List Bool), U wTmp1 = [] →
      ∃ lL : List Bool, lL.length = 2 * l.length * (U wT).length + (U wL).length ∧
        l.foldl (fun W _ => copyT2WExec W) U = Function.update U wL lL ∧
        forEachCost wTmp2 (fun _ => copyT2WExec) (fun _ => copyT2WCost) l U ≤
          l.length * (14 * (U wT).length + 6) + 1 := by
    intro l
    induction l with
    | nil =>
      intro U _
      exact ⟨U wL, by simp, by simp [Function.update_eq_self], by simp [forEachCost]⟩
    | cons _ l ih =>
      intro U hU1
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have h1 := hcopy2 U hU1
      have h1' := hcopy2 (Function.update U wTmp2 l) (by simp [Fin.ext_iff, hU1])
      obtain ⟨lL, hlL, hfe, _⟩ := ih (copyT2WExec U) (by rw [h1.1]; simp [Fin.ext_iff, hU1])
      obtain ⟨_, _, _, hfc⟩ := ih (copyT2WExec (Function.update U wTmp2 l)) (by rw [h1'.1]; simp [Fin.ext_iff, hU1])
      refine ⟨lL, ?_, ?_, ?_⟩
      · rw [hlL, h1.1]; simp only [Function.update_self, Function.update_of_ne (by decide : wT ≠ wL),
          List.length_append]
        have hmul : 2 * (l.length + 1) * (U wT).length = 2 * l.length * (U wT).length + 2 * (U wT).length := by ring
        omega
      · rw [hfe, h1.1, Function.update_idem]
      · have hT1 : (copyT2WExec (Function.update U wTmp2 l) wT).length = (U wT).length := by
          rw [h1'.1]; simp [Fin.ext_iff]
        rw [hT1] at hfc
        have hc2 := h1'.2
        simp only [Function.update_of_ne (by decide : wT ≠ wTmp2)] at hc2
        have hmul : (l.length + 1) * (14 * (U wT).length + 6) =
            l.length * (14 * (U wT).length + 6) + (14 * (U wT).length + 6) := by ring
        omega
  let S1 := Function.update S wL (true :: true :: S wL)
  have hS2 : copyExec wV wTmp2 wTmp1 S1 = Function.update S1 wTmp2 (S wV) := by
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S1 (by simp [S1, Fin.ext_iff, ht1])]
    simp [S1, Fin.ext_iff, ht2]
  have hS2t : (copyExec wV wTmp2 wTmp1 S1) wTmp2 = S wV := by rw [hS2]; simp
  obtain ⟨lL, hlL, hfe, _⟩ := hfold (S wV) (Function.update (copyExec wV wTmp2 wTmp1 S1) wTmp2 [])
    (by rw [hS2]; simp [S1, Fin.ext_iff, ht1])
  obtain ⟨_, _, _, hfc⟩ := hfold (S wV) (copyExec wV wTmp2 wTmp1 S1)
    (by rw [hS2]; simp [S1, Fin.ext_iff, ht1])
  have hlLeq : lL.length = L := by
    rw [hlL, hS2]; simp [S1, Fin.ext_iff, hV, hT, hL, L]; ring
  have hS3 : ((copyExec wV wTmp2 wTmp1 S1) wTmp2).foldl (fun U _ => copyT2WExec U)
      (Function.update (copyExec wV wTmp2 wTmp1 S1) wTmp2 []) =
      Function.update S wL lL := by
    rw [hS2t, hfe, hS2]
    funext j
    by_cases j1 : j = wL; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = wTmp2; · subst j2; simp [S1, Fin.ext_iff, ht2]
    simp [S1, Fin.ext_iff, j1, j2]
  have hS4 : clearExec wT (((copyExec wV wTmp2 wTmp1 S1) wTmp2).foldl (fun U _ => copyT2WExec U)
      (Function.update (copyExec wV wTmp2 wTmp1 S1) wTmp2 [])) =
      Function.update (Function.update S wT []) wL lL := by
    rw [hS3]; funext j; simp only [clearExec]
    by_cases j1 : j = wL; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = wT; · subst j2; simp [Fin.ext_iff]
    simp [Fin.ext_iff, j1, j2]
  have hS6 : Function.update (copyExec wL wL1 wTmp1 (clearExec wT
      (((copyExec wV wTmp2 wTmp1 S1) wTmp2).foldl (fun U _ => copyT2WExec U)
        (Function.update (copyExec wV wTmp2 wTmp1 S1) wTmp2 [])))) wL1
      (true :: copyExec wL wL1 wTmp1 (clearExec wT
        (((copyExec wV wTmp2 wTmp1 S1) wTmp2).foldl (fun U _ => copyT2WExec U)
          (Function.update (copyExec wV wTmp2 wTmp1 S1) wTmp2 []))) wL1) =
      Function.update (Function.update (Function.update S wT []) wL lL) wL1 (true :: lL) := by
    rw [hS4, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, ht1])]
    simp [Fin.ext_iff, hL1]
  refine ⟨lL, true :: lL, lL.tail, hlLeq, by simp [hlLeq], by simp [hlLeq], ?_, ?_⟩
  · simp only [wStageBExec]
    rw [hS6, copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, ht1])]
    simp [Fin.ext_iff, hLm1]
  · simp only [wStageBCost]
    rw [hS6, hS4, hS3, hS2t]
    have hS2T : (copyExec wV wTmp2 wTmp1 S1 wT).length = t := by rw [hS2]; simp [S1, Fin.ext_iff, hT]
    rw [hS2T] at hfc
    simp only [S1, Function.update_self, Function.update_of_ne (by decide : wL ≠ wL1),
      Function.update_of_ne (by decide : wTmp1 ≠ wL1), Function.update_of_ne (by decide : wTmp1 ≠ wL),
      Function.update_of_ne (by decide : wTmp1 ≠ wT), Function.update_of_ne (by decide : wT ≠ wL),
      Function.update_of_ne (by decide : wV ≠ wL),
      hV, hT, ht1, hlLeq, List.length_nil] at hfc ⊢
    have hmul : v * (14 * t + 6) = 14 * v * t + 6 * v := by ring
    have hmul2 : 14 * v * t ≤ 16 * v * t := Nat.mul_le_mul_right _ (by omega)
    omega

theorem wStageC_spec (S : WK → List Bool) (n v L : ℕ)
    (hN : (S wN).length = n) (hV : (S wV).length = v) (hL1 : (S wL1).length = L + 1)
    (hT : S wT = []) (hBlk : S wBlk = []) (hO : S wOutRev = []) (hX : S wX = [])
    (hRL : S wRemLeft = []) (hRA : S wRemAll = []) (ht1 : S wTmp1 = []) (ht2 : S wTmp2 = []) :
    let k := v * (L + 1)
    let w := k.bits.length
    wStageCExec S =
      Function.update (Function.update (Function.update (Function.update (Function.update S wV [])
        wOutRev (false :: List.replicate k true)) wX (fieldBits w 0))
        wRemLeft (S wN)) wRemAll (S wV) ∧
    wStageCCost S ≤ 5 * (k + 1) ^ 2 + 30 * (k + 1) + 10 * v * (L + 1) + 25 * v + 7 * n + 20 := by
  intro k w
  have hS1 : copyExec wV wTmp2 wTmp1 S = Function.update S wTmp2 (S wV) := by
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S ht1, ht2, List.append_nil]
  have hmulFold : ∀ (l : List Bool) (U : WK → List Bool), U wTmp1 = [] →
      ∃ lB : List Bool, lB.length = l.length * (U wL1).length + (U wBlk).length ∧
        l.foldl (fun W _ => copyExec wL1 wBlk wTmp1 W) U = Function.update U wBlk lB ∧
        forEachCost wTmp2 (fun _ => copyExec wL1 wBlk wTmp1)
          (fun _ W => 7 * (W wL1).length + 4 * (W wTmp1).length + 2) l U ≤
          l.length * (7 * (U wL1).length + 4) + 1 := by
    intro l
    induction l with
    | nil =>
      intro U _
      exact ⟨U wBlk, by simp, by simp [Function.update_eq_self], by simp [forEachCost]⟩
    | cons _ l ih =>
      intro U hU1
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have hc1 : copyExec wL1 wBlk wTmp1 U = Function.update U wBlk (U wL1 ++ U wBlk) :=
        copyExec_of_empty (by decide) (by decide) (by decide) U hU1
      have hc2 : copyExec wL1 wBlk wTmp1 (Function.update U wTmp2 l) =
          Function.update (Function.update U wTmp2 l) wBlk (U wL1 ++ U wBlk) := by
        rw [copyExec_of_empty (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, hU1])]
        simp [Fin.ext_iff]
      obtain ⟨lB, hlB, hfe, _⟩ := ih (copyExec wL1 wBlk wTmp1 U) (by rw [hc1]; simp [Fin.ext_iff, hU1])
      obtain ⟨_, _, _, hfc⟩ := ih (copyExec wL1 wBlk wTmp1 (Function.update U wTmp2 l))
        (by rw [hc2]; simp [Fin.ext_iff, hU1])
      refine ⟨lB, ?_, ?_, ?_⟩
      · rw [hlB, hc1]; simp only [Function.update_self, Function.update_of_ne (by decide : wL1 ≠ wBlk),
          List.length_append]
        have h1 : (l.length + 1) * (U wL1).length = l.length * (U wL1).length + (U wL1).length := by ring
        omega
      · rw [hfe, hc1, Function.update_idem]
      · have hL1' : (copyExec wL1 wBlk wTmp1 (Function.update U wTmp2 l) wL1).length = (U wL1).length := by
          rw [hc2]; simp [Fin.ext_iff]
        rw [hL1'] at hfc
        simp only [Function.update_of_ne (by decide : wL1 ≠ wTmp2),
          Function.update_of_ne (by decide : wTmp1 ≠ wTmp2), hU1, List.length_nil] at hfc ⊢
        have h1 : (l.length + 1) * (7 * (U wL1).length + 4) =
            l.length * (7 * (U wL1).length + 4) + (7 * (U wL1).length + 4) := by ring
        omega
  have hS1t : (copyExec wV wTmp2 wTmp1 S) wTmp2 = S wV := by rw [hS1]; simp
  obtain ⟨lB, hlB, hfeB, _⟩ := hmulFold (S wV) (Function.update (copyExec wV wTmp2 wTmp1 S) wTmp2 [])
    (by rw [hS1]; simp [Fin.ext_iff, ht1])
  obtain ⟨_, _, _, hfcB⟩ := hmulFold (S wV) (copyExec wV wTmp2 wTmp1 S)
    (by rw [hS1]; simp [Fin.ext_iff, ht1])
  have hlBeq : lB.length = k := by rw [hlB, hS1]; simp [Fin.ext_iff, hV, hL1, hBlk, k]
  have hS2 : ((copyExec wV wTmp2 wTmp1 S) wTmp2).foldl (fun U _ => copyExec wL1 wBlk wTmp1 U)
      (Function.update (copyExec wV wTmp2 wTmp1 S) wTmp2 []) =
      Function.update S wBlk lB := by
    rw [hS1t, hfeB, hS1]
    funext j
    by_cases j1 : j = wBlk; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = wTmp2; · subst j2; simp [Fin.ext_iff, ht2]
    simp [Fin.ext_iff, j1, j2]
  have hkhdr : ∀ (l : List Bool) (m : ℕ) (U : WK → List Bool),
      U wT = m.bits → U wTmp1 = [] →
      l.foldl (fun W _ => kHdrStepExec W) U =
        Function.update (Function.update U wOutRev (List.replicate l.length true ++ U wOutRev))
          wT (m + l.length).bits ∧
      forEachCost wBlk (fun _ => kHdrStepExec) (fun _ => kHdrStepCost) l U ≤
        l.length * (5 * (m + l.length) + 10) + 1 := by
    intro l
    induction l with
    | nil =>
      intro m U hUT _
      refine ⟨?_, by simp [forEachCost]⟩
      funext j
      by_cases j1 : j = wT; · subst j1; simp [Fin.ext_iff, hUT]
      by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff]
      simp [Fin.ext_iff, j1, j2]
    | cons _ l ih =>
      intro m U hUT hU1
      simp only [List.foldl_cons, List.length_cons, forEachCost]
      have hs1 : kHdrStepExec U =
          Function.update (Function.update U wOutRev (true :: U wOutRev)) wT (m + 1).bits := by
        simp only [kHdrStepExec]
        rw [incBinExec_of_empty (by decide) _ (by simp [Fin.ext_iff, hU1]),
            Function.update_of_ne (by decide), hUT, incBits_bits]
      have hs2 : kHdrStepExec (Function.update U wBlk l) =
          Function.update (Function.update (Function.update U wBlk l) wOutRev (true :: U wOutRev)) wT (m + 1).bits := by
        simp only [kHdrStepExec]
        rw [incBinExec_of_empty (by decide) _ (by simp [Fin.ext_iff, hU1]),
            Function.update_of_ne (by decide), Function.update_of_ne (by decide),
            Function.update_of_ne (by decide), hUT, incBits_bits]
      have hr1 := ih (m + 1) (kHdrStepExec U) (by rw [hs1]; simp) (by rw [hs1]; simp [Fin.ext_iff, hU1])
      have hr2 := ih (m + 1) (kHdrStepExec (Function.update U wBlk l))
        (by rw [hs2]; simp) (by rw [hs2]; simp [Fin.ext_iff, hU1])
      refine ⟨?_, ?_⟩
      · rw [hr1.1, hs1]
        funext j
        by_cases j1 : j = wT
        · subst j1; simp [Fin.ext_iff, show m + 1 + l.length = m + (l.length + 1) by omega]
        by_cases j2 : j = wOutRev
        · subst j2; simp [Fin.ext_iff, List.replicate_succ, replicate_append_cons]
        simp [Fin.ext_iff, j1, j2]
      · have hcost1 : kHdrStepCost (Function.update U wBlk l) ≤ 5 * m + 8 := by
          simp only [kHdrStepCost, Function.update_of_ne (by decide : wT ≠ wOutRev),
            Function.update_of_ne (by decide : wT ≠ wBlk),
            Function.update_of_ne (by decide : wTmp1 ≠ wOutRev),
            Function.update_of_ne (by decide : wTmp1 ≠ wBlk), hUT, hU1, List.length_nil]
          have := bits_length_le m; omega
        have hc2 := hr2.2
        rw [show m + 1 + l.length = m + (l.length + 1) by omega] at hc2
        have h1 : (l.length + 1) * (5 * (m + (l.length + 1)) + 10) =
            l.length * (5 * (m + (l.length + 1)) + 10) + (5 * (m + (l.length + 1)) + 10) := by ring
        omega
  have hk1 := hkhdr lB 0 (Function.update (Function.update S wBlk lB) wBlk [])
    (by simp [Fin.ext_iff, hT]) (by simp [Fin.ext_iff, ht1])
  have hk2 := hkhdr lB 0 (Function.update S wBlk lB)
    (by simp [Fin.ext_iff, hT]) (by simp [Fin.ext_iff, ht1])
  have hS4 : Function.update (((Function.update S wBlk lB) wBlk).foldl (fun U _ => kHdrStepExec U)
      (Function.update (Function.update S wBlk lB) wBlk [])) wOutRev
      (false :: (((Function.update S wBlk lB) wBlk).foldl (fun U _ => kHdrStepExec U)
        (Function.update (Function.update S wBlk lB) wBlk [])) wOutRev) =
      Function.update (Function.update S wOutRev (false :: List.replicate k true)) wT k.bits := by
    simp only [Function.update_self]; rw [hk1.1]
    funext j
    by_cases j1 : j = wT; · subst j1; simp [Fin.ext_iff, hlBeq]
    by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff, hlBeq, hO]
    by_cases j3 : j = wBlk; · subst j3; simp [Fin.ext_iff, hBlk]
    simp [Fin.ext_iff, j1, j2, j3]
  have hpushF : ∀ (l : List Bool) (U : WK → List Bool),
      l.foldl (fun W _ => Function.update W wX (false :: W wX)) U =
        Function.update U wX (List.replicate l.length false ++ U wX) := by
    intro l
    induction l with
    | nil => intro U; simp [Function.update_eq_self]
    | cons _ l ih =>
      intro U; simp only [List.foldl_cons, List.length_cons]; rw [ih]
      funext j
      by_cases j1 : j = wX
      · subst j1; simp [List.replicate_succ, replicate_append_cons]
      · simp [j1]
  have hS5 : ((Function.update (Function.update S wOutRev (false :: List.replicate k true)) wT k.bits) wT).foldl
      (fun U _ => Function.update U wX (false :: U wX))
      (Function.update (Function.update (Function.update S wOutRev (false :: List.replicate k true)) wT k.bits) wT []) =
      Function.update (Function.update S wOutRev (false :: List.replicate k true)) wX (fieldBits w 0) := by
    simp only [Function.update_self]; rw [hpushF]
    funext j
    by_cases j1 : j = wX; · subst j1; simp [Fin.ext_iff, hX, fieldBits_zero, w]
    by_cases j2 : j = wT; · subst j2; simp [Fin.ext_iff, hT]
    by_cases j3 : j = wOutRev; · subst j3; simp [Fin.ext_iff]
    simp [Fin.ext_iff, j1, j2, j3]
  refine ⟨?_, ?_⟩
  · simp only [wStageCExec]
    rw [hS2, hS4, hS5]
    rw [copyExec_of_empty (a := wN) (b := wRemLeft) (tmp := wTmp1) (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, ht1])]
    rw [copyExec_of_empty (a := wV) (b := wRemAll) (tmp := wTmp1) (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, ht1])]
    funext j; simp only [clearExec]
    by_cases j1 : j = wRemAll; · subst j1; simp [Fin.ext_iff, hRA]
    by_cases j2 : j = wRemLeft; · subst j2; simp [Fin.ext_iff, hRL]
    by_cases j3 : j = wX; · subst j3; simp [Fin.ext_iff]
    by_cases j4 : j = wOutRev; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = wV; · subst j5; simp [Fin.ext_iff]
    simp [Fin.ext_iff, j1, j2, j3, j4, j5]
  · simp only [wStageCCost]
    rw [hS2, hS4, hS5, hS1t]
    rw [copyExec_of_empty (a := wN) (b := wRemLeft) (tmp := wTmp1) (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, ht1])]
    rw [copyExec_of_empty (a := wV) (b := wRemAll) (tmp := wTmp1) (by decide) (by decide) (by decide) _ (by simp [Fin.ext_iff, ht1])]
    have hcx := forEachCost_le wT (fun _ U => Function.update U wX (false :: U wX)) (fun _ _ => 1)
      (fun _ => True) 1 (fun _ _ _ => trivial) (fun _ _ _ => le_rfl) (fun _ _ _ => trivial)
      k.bits (Function.update (Function.update S wOutRev (false :: List.replicate k true)) wT k.bits) trivial
    have hck := hk2.2
    have hS1L1 : (copyExec wV wTmp2 wTmp1 S wL1).length = L + 1 := by rw [hS1]; simp [Fin.ext_iff, hL1]
    rw [hS1L1] at hfcB
    simp only [Function.update_self, Function.update_of_ne (by decide : wV ≠ wRemAll),
      Function.update_of_ne (by decide : wV ≠ wRemLeft), Function.update_of_ne (by decide : wV ≠ wX),
      Function.update_of_ne (by decide : wV ≠ wOutRev), Function.update_of_ne (by decide : wTmp1 ≠ wRemLeft),
      Function.update_of_ne (by decide : wTmp1 ≠ wX), Function.update_of_ne (by decide : wTmp1 ≠ wOutRev),
      Function.update_of_ne (by decide : wN ≠ wX), Function.update_of_ne (by decide : wN ≠ wOutRev),
      hV, hN, hL1, ht1, hlBeq, List.length_nil] at hcx hck hfcB ⊢
    have hwk : k.bits.length ≤ k := bits_length_le k
    have hmul1 : k * (5 * (0 + k) + 10) ≤ (k + 1) * (5 * (k + 1) + 10) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hmul1' : (k + 1) * (5 * (k + 1) + 10) = 5 * (k + 1) ^ 2 + 10 * (k + 1) := by ring
    have hmul2 : v * (7 * (L + 1) + 4) = 7 * v * (L + 1) + 4 * v := by ring
    have hmul3 : 7 * v * (L + 1) ≤ 10 * v * (L + 1) := Nat.mul_le_mul_right _ (by omega)
    omega

theorem leftFold_spec (n L w : ℕ) (hL2 : 2 ≤ L) :
    ∀ (lp : List Bool) (x0 remAll : ℕ) (U : WK → List Bool),
      lp.length ≤ remAll →
      (U wN).length = n → (U wL).length = L → (U wL1).length = L + 1 → (U wLm1).length = L - 1 →
      (U wRemLeft).length = lp.length → (U wRemAll).length = remAll →
      U wX = fieldBits w x0 → U wY = [] → U wRemR = [] → U wRow = [] →
      U wCnt = [] → U wBlk = [] → U wRxLoop = [] → U wTmp1 = [] → U wTmp2 = [] →
      lp.foldl (fun W _ => leftBlockExec W) U =
        Function.update (Function.update (Function.update (Function.update (Function.update U
          wRemLeft []) wRemAll ((U wRemAll).drop lp.length)) wIn ((U wIn).drop (lp.length * n)))
          wOutRev ((emitLeftBlocks w L n lp.length x0 remAll (U wIn)).reverse ++ U wOutRev))
          wX (fieldBits w (x0 + lp.length * (L + 1))) ∧
      forEachCost wNloop (fun _ => leftBlockExec) (fun _ => leftBlockCost) lp U ≤
        lp.length * ((L + 1) * ((L + 1 + (lp.length + n + remAll) * (L + 1)) * (19 * w + 20) +
          12 * (lp.length + n + remAll) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 22) + 1 := by
  intro lp
  induction lp with
  | nil =>
    intro x0 remAll U _ _ _ _ _ hRL _ hUX _ _ _ _ _ _ _ _
    have hRL0 : U wRemLeft = [] := List.eq_nil_of_length_eq_zero hRL
    refine ⟨?_, by simp [forEachCost]⟩
    funext j
    by_cases j1 : j = wX; · subst j1; simp [Fin.ext_iff, hUX]
    by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff, emitLeftBlocks]
    by_cases j3 : j = wIn; · subst j3; simp [Fin.ext_iff]
    by_cases j4 : j = wRemAll; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = wRemLeft; · subst j5; simp [Fin.ext_iff, hRL0]
    simp [Fin.ext_iff, j1, j2, j3, j4, j5]
  | cons _ lp ih =>
    intro x0 remAll U hle hUN hUL hUL1 hULm1 hRL hRA hUX hUY hURR hURow hUC hUB hURx hUt1 hUt2
    simp only [List.foldl_cons, List.length_cons, forEachCost] at hle hRL ⊢
    obtain ⟨ra, hra⟩ : ∃ ra, remAll = ra + 1 := ⟨remAll - 1, by omega⟩
    subst hra
    have h1 := leftBlock_spec U w x0 L n lp.length ra hL2 hUN hUL hUL1 hULm1 hRL hRA
      hUX hUY hURR hURow hUC hUB hURx hUt1 hUt2
    have h1' := leftBlock_spec (Function.update U wNloop lp) w x0 L n lp.length ra hL2
      (by simp [Fin.ext_iff, hUN]) (by simp [Fin.ext_iff, hUL]) (by simp [Fin.ext_iff, hUL1])
      (by simp [Fin.ext_iff, hULm1]) (by simp [Fin.ext_iff, hRL]) (by simp [Fin.ext_iff, hRA])
      (by simp [Fin.ext_iff, hUX]) (by simp [Fin.ext_iff, hUY]) (by simp [Fin.ext_iff, hURR])
      (by simp [Fin.ext_iff, hURow]) (by simp [Fin.ext_iff, hUC]) (by simp [Fin.ext_iff, hUB])
      (by simp [Fin.ext_iff, hURx]) (by simp [Fin.ext_iff, hUt1]) (by simp [Fin.ext_iff, hUt2])
    have htlL : (U wRemLeft).tail.length = lp.length := by rw [List.length_tail, hRL]; omega
    have htlA : (U wRemAll).tail.length = ra := by rw [List.length_tail, hRA]; omega
    have hr1 := ih (x0 + L + 1) ra (leftBlockExec U) (by omega)
      (by rw [h1.1]; simp [Fin.ext_iff, hUN]) (by rw [h1.1]; simp [Fin.ext_iff, hUL])
      (by rw [h1.1]; simp [Fin.ext_iff, hUL1]) (by rw [h1.1]; simp [Fin.ext_iff, hULm1])
      (by rw [h1.1]; simp [Fin.ext_iff, htlL]) (by rw [h1.1]; simp [Fin.ext_iff, htlA])
      (by rw [h1.1]; simp [Fin.ext_iff]) (by rw [h1.1]; simp [Fin.ext_iff, hUY])
      (by rw [h1.1]; simp [Fin.ext_iff, hURR]) (by rw [h1.1]; simp [Fin.ext_iff, hURow])
      (by rw [h1.1]; simp [Fin.ext_iff, hUC]) (by rw [h1.1]; simp [Fin.ext_iff, hUB])
      (by rw [h1.1]; simp [Fin.ext_iff, hURx]) (by rw [h1.1]; simp [Fin.ext_iff, hUt1])
      (by rw [h1.1]; simp [Fin.ext_iff, hUt2])
    have hr2 := ih (x0 + L + 1) ra (leftBlockExec (Function.update U wNloop lp)) (by omega)
      (by rw [h1'.1]; simp [Fin.ext_iff, hUN]) (by rw [h1'.1]; simp [Fin.ext_iff, hUL])
      (by rw [h1'.1]; simp [Fin.ext_iff, hUL1]) (by rw [h1'.1]; simp [Fin.ext_iff, hULm1])
      (by rw [h1'.1]; simp [Fin.ext_iff, htlL]) (by rw [h1'.1]; simp [Fin.ext_iff, htlA])
      (by rw [h1'.1]; simp [Fin.ext_iff]) (by rw [h1'.1]; simp [Fin.ext_iff, hUY])
      (by rw [h1'.1]; simp [Fin.ext_iff, hURR]) (by rw [h1'.1]; simp [Fin.ext_iff, hURow])
      (by rw [h1'.1]; simp [Fin.ext_iff, hUC]) (by rw [h1'.1]; simp [Fin.ext_iff, hUB])
      (by rw [h1'.1]; simp [Fin.ext_iff, hURx]) (by rw [h1'.1]; simp [Fin.ext_iff, hUt1])
      (by rw [h1'.1]; simp [Fin.ext_iff, hUt2])
    refine ⟨?_, ?_⟩
    · rw [hr1.1, h1.1]
      have hdropA : (U wRemAll).tail.drop lp.length = (U wRemAll).drop (lp.length + 1) := by
        cases U wRemAll <;> simp
      have hdropIn : ((U wIn).drop n).drop (lp.length * n) = (U wIn).drop ((lp.length + 1) * n) := by
        rw [List.drop_drop, show n + lp.length * n = (lp.length + 1) * n by ring]
      funext j
      by_cases j1 : j = wX
      · subst j1; simp [Fin.ext_iff, show x0 + L + 1 + lp.length * (L + 1) = x0 + (lp.length + 1) * (L + 1) by ring]
      by_cases j2 : j = wOutRev
      · subst j2; simp [Fin.ext_iff, emitLeftBlocks, List.reverse_append, List.append_assoc]
      by_cases j3 : j = wIn; · subst j3; simp [Fin.ext_iff, hdropIn]
      by_cases j4 : j = wRemAll; · subst j4; simp [Fin.ext_iff, hdropA]
      by_cases j5 : j = wRemLeft; · subst j5; simp [Fin.ext_iff]
      simp [Fin.ext_iff, j1, j2, j3, j4, j5]
    · set M := (L + 1) * ((L + 1 + (lp.length + 1 + n + (ra + 1)) * (L + 1)) * (19 * w + 20) +
          12 * (lp.length + 1 + n + (ra + 1)) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 22
      have hM1 : leftBlockCost (Function.update U wNloop lp) + 2 ≤ M := by
        have hc1 := h1'.2
        have hsub : (L + 1 + (lp.length + n + ra) * (L + 1)) * (19 * w + 20) ≤
            (L + 1 + (lp.length + 1 + n + (ra + 1)) * (L + 1)) * (19 * w + 20) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
        have hsub2 := Nat.mul_le_mul_left (L + 1) (show (L + 1 + (lp.length + n + ra) * (L + 1)) * (19 * w + 20) +
            12 * (lp.length + n + ra) + 21 * (L + 1) + 25 * w + 50 ≤
            (L + 1 + (lp.length + 1 + n + (ra + 1)) * (L + 1)) * (19 * w + 20) +
            12 * (lp.length + 1 + n + (ra + 1)) + 21 * (L + 1) + 25 * w + 50 by omega)
        omega
      have hM2 : forEachCost wNloop (fun _ => leftBlockExec) (fun _ => leftBlockCost) lp
          (leftBlockExec (Function.update U wNloop lp)) ≤ lp.length * M + 1 := by
        have hc2 := hr2.2
        have hsub : (L + 1 + (lp.length + n + ra) * (L + 1)) * (19 * w + 20) ≤
            (L + 1 + (lp.length + 1 + n + (ra + 1)) * (L + 1)) * (19 * w + 20) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
        have hsub2 : (L + 1) * ((L + 1 + (lp.length + n + ra) * (L + 1)) * (19 * w + 20) +
            12 * (lp.length + n + ra) + 21 * (L + 1) + 25 * w + 50) ≤
            (L + 1) * ((L + 1 + (lp.length + 1 + n + (ra + 1)) * (L + 1)) * (19 * w + 20) +
            12 * (lp.length + 1 + n + (ra + 1)) + 21 * (L + 1) + 25 * w + 50) :=
          Nat.mul_le_mul_left (L + 1) (by omega)
        have hsub3 : lp.length * ((L + 1) * ((L + 1 + (lp.length + n + ra) * (L + 1)) * (19 * w + 20) +
            12 * (lp.length + n + ra) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 22) ≤ lp.length * M :=
          Nat.mul_le_mul_left lp.length (Nat.add_le_add_right (Nat.add_le_add_right hsub2 _) _)
        exact le_trans hc2 (Nat.add_le_add_right hsub3 1)
      have hmul : (lp.length + 1) * M = lp.length * M + M := by ring
      have hsum : leftBlockCost (Function.update U wNloop lp) + 2 +
          forEachCost wNloop (fun _ => leftBlockExec) (fun _ => leftBlockCost) lp
            (leftBlockExec (Function.update U wNloop lp)) ≤ M + (lp.length * M + 1) :=
        Nat.add_le_add hM1 hM2
      omega

theorem rightFold_spec (L w : ℕ) :
    ∀ (lp : List Bool) (x0 : ℕ) (U : WK → List Bool),
      (U wL1).length = L + 1 → (U wRemAll).length = lp.length →
      U wX = fieldBits w x0 → U wY = [] → U wRemR = [] →
      U wCnt = [] → U wBlk = [] → U wRxLoop = [] → U wTmp1 = [] →
      lp.foldl (fun W _ => rightBlockExec W) U =
        Function.update (Function.update (Function.update U wRemAll [])
          wOutRev ((emitRightBlocks w L lp.length x0 lp.length).reverse ++ U wOutRev))
          wX (fieldBits w (x0 + lp.length * (L + 1))) ∧
      forEachCost wNloop (fun _ => rightBlockExec) (fun _ => rightBlockCost) lp U ≤
        lp.length * ((L + 1) * ((L + 1 + lp.length * (L + 1)) * (19 * w + 20) +
          12 * lp.length + 7 * (L + 1) + 25 * w + 37) + 14 * (L + 1) + 12) + 1 := by
  intro lp
  induction lp with
  | nil =>
    intro x0 U _ hRA hUX _ _ _ _ _ _
    have hRA0 : U wRemAll = [] := List.eq_nil_of_length_eq_zero hRA
    refine ⟨?_, by simp [forEachCost]⟩
    funext j
    by_cases j1 : j = wX; · subst j1; simp [Fin.ext_iff, hUX]
    by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff, emitRightBlocks]
    by_cases j3 : j = wRemAll; · subst j3; simp [Fin.ext_iff, hRA0]
    simp [Fin.ext_iff, j1, j2, j3]
  | cons _ lp ih =>
    intro x0 U hUL1 hRA hUX hUY hURR hUC hUB hURx hUt1
    simp only [List.foldl_cons, List.length_cons, forEachCost] at hRA ⊢
    have h1 := rightBlock_spec U w x0 L lp.length hUL1 hRA hUX hUY hURR hUC hUB hURx hUt1
    have h1' := rightBlock_spec (Function.update U wNloop lp) w x0 L lp.length
      (by simp [Fin.ext_iff, hUL1]) (by simp [Fin.ext_iff, hRA]) (by simp [Fin.ext_iff, hUX])
      (by simp [Fin.ext_iff, hUY]) (by simp [Fin.ext_iff, hURR]) (by simp [Fin.ext_iff, hUC])
      (by simp [Fin.ext_iff, hUB]) (by simp [Fin.ext_iff, hURx]) (by simp [Fin.ext_iff, hUt1])
    have htlA : (U wRemAll).tail.length = lp.length := by rw [List.length_tail, hRA]; omega
    have hr1 := ih (x0 + L + 1) (rightBlockExec U)
      (by rw [h1.1]; simp [Fin.ext_iff, hUL1]) (by rw [h1.1]; simp [Fin.ext_iff, htlA])
      (by rw [h1.1]; simp [Fin.ext_iff]) (by rw [h1.1]; simp [Fin.ext_iff, hUY])
      (by rw [h1.1]; simp [Fin.ext_iff, hURR]) (by rw [h1.1]; simp [Fin.ext_iff, hUC])
      (by rw [h1.1]; simp [Fin.ext_iff, hUB]) (by rw [h1.1]; simp [Fin.ext_iff, hURx])
      (by rw [h1.1]; simp [Fin.ext_iff, hUt1])
    have hr2 := ih (x0 + L + 1) (rightBlockExec (Function.update U wNloop lp))
      (by rw [h1'.1]; simp [Fin.ext_iff, hUL1]) (by rw [h1'.1]; simp [Fin.ext_iff, htlA])
      (by rw [h1'.1]; simp [Fin.ext_iff]) (by rw [h1'.1]; simp [Fin.ext_iff, hUY])
      (by rw [h1'.1]; simp [Fin.ext_iff, hURR]) (by rw [h1'.1]; simp [Fin.ext_iff, hUC])
      (by rw [h1'.1]; simp [Fin.ext_iff, hUB]) (by rw [h1'.1]; simp [Fin.ext_iff, hURx])
      (by rw [h1'.1]; simp [Fin.ext_iff, hUt1])
    refine ⟨?_, ?_⟩
    · rw [hr1.1, h1.1]
      funext j
      by_cases j1 : j = wX
      · subst j1; simp [Fin.ext_iff, show x0 + L + 1 + lp.length * (L + 1) = x0 + (lp.length + 1) * (L + 1) by ring]
      by_cases j2 : j = wOutRev
      · subst j2; simp [Fin.ext_iff, emitRightBlocks, List.reverse_append, List.append_assoc]
      by_cases j3 : j = wRemAll; · subst j3; simp [Fin.ext_iff]
      simp [Fin.ext_iff, j1, j2, j3]
    · set M := (L + 1) * ((L + 1 + (lp.length + 1) * (L + 1)) * (19 * w + 20) +
          12 * (lp.length + 1) + 7 * (L + 1) + 25 * w + 37) + 14 * (L + 1) + 12
      have hM1 : rightBlockCost (Function.update U wNloop lp) + 2 ≤ M := by
        have hc1 := h1'.2
        have hsub : (L + 1 + lp.length * (L + 1)) * (19 * w + 20) ≤
            (L + 1 + (lp.length + 1) * (L + 1)) * (19 * w + 20) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
        have hsub2 := Nat.mul_le_mul_left (L + 1) (show (L + 1 + lp.length * (L + 1)) * (19 * w + 20) +
            12 * lp.length + 7 * (L + 1) + 25 * w + 37 ≤
            (L + 1 + (lp.length + 1) * (L + 1)) * (19 * w + 20) +
            12 * (lp.length + 1) + 7 * (L + 1) + 25 * w + 37 by omega)
        omega
      have hM2 : forEachCost wNloop (fun _ => rightBlockExec) (fun _ => rightBlockCost) lp
          (rightBlockExec (Function.update U wNloop lp)) ≤ lp.length * M + 1 := by
        have hc2 := hr2.2
        have hsub : (L + 1 + lp.length * (L + 1)) * (19 * w + 20) ≤
            (L + 1 + (lp.length + 1) * (L + 1)) * (19 * w + 20) :=
          Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
        have hsub2 : (L + 1) * ((L + 1 + lp.length * (L + 1)) * (19 * w + 20) +
            12 * lp.length + 7 * (L + 1) + 25 * w + 37) ≤
            (L + 1) * ((L + 1 + (lp.length + 1) * (L + 1)) * (19 * w + 20) +
            12 * (lp.length + 1) + 7 * (L + 1) + 25 * w + 37) :=
          Nat.mul_le_mul_left (L + 1) (by omega)
        have hsub3 : lp.length * ((L + 1) * ((L + 1 + lp.length * (L + 1)) * (19 * w + 20) +
            12 * lp.length + 7 * (L + 1) + 25 * w + 37) + 14 * (L + 1) + 12) ≤ lp.length * M :=
          Nat.mul_le_mul_left lp.length (Nat.add_le_add_right (Nat.add_le_add_right hsub2 _) _)
        exact le_trans hc2 (Nat.add_le_add_right hsub3 1)
      have hmul : (lp.length + 1) * M = lp.length * M + M := by ring
      have hsum : rightBlockCost (Function.update U wNloop lp) + 2 +
          forEachCost wNloop (fun _ => rightBlockExec) (fun _ => rightBlockCost) lp
            (rightBlockExec (Function.update U wNloop lp)) ≤ M + (lp.length * M + 1) :=
        Nat.add_le_add hM1 hM2
      omega

theorem write_poly_bound (inpLen n aLen v t L k w wfLen cA cB cC cD : ℕ)
    (hnLen : n ≤ inpLen) (haLen : aLen ≤ inpLen) (hv : v = 2 * n)
    (ht : t ≤ v + 1) (hL : L = 2 * (1 + v * t)) (hk : k = v * (L + 1)) (hw : w ≤ k)
    (hwfLen : wfLen ≤ k + 1 + n * (L + 1) * (L + 1 + (n + n + v) * (L + 1)) * (2 * w) +
      n * (L + 1) * (L + 1 + n * (L + 1)) * (2 * w))
    (hcA : cA ≤ 5 * (v + 1) ^ 2 + 30 * (v + 1) + 2 * inpLen + 30)
    (hcB : cB ≤ 16 * v * t + 14 * L + 14 * v + 3 * t + 20)
    (hcC : cC ≤ 5 * (k + 1) ^ 2 + 30 * (k + 1) + 10 * v * (L + 1) + 25 * v + 7 * n + 20)
    (hcD : cD ≤ 3 * wfLen + 3 * w + 3 * L + 3 * (L + 1) + 3 * (L - 1) + 17 * n + 3 * aLen +
      n * ((L + 1) * ((L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
        12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 22) +
      n * ((L + 1) * ((L + 1 + n * (L + 1)) * (19 * w + 20) +
        12 * n + 7 * (L + 1) + 25 * w + 37) + 14 * (L + 1) + 12) + 30) :
    1 + (cD + (cC + (cB + cA))) ≤ 5000000000 * (inpLen + 1) ^ 9 := by
  set N := inpLen + 1
  have hN1 : 1 ≤ N := by omega
  have hN2 : N ≤ N ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_right N (by omega)
  have hN3 : N ^ 2 ≤ N ^ 3 := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
  have h1_N2 : 1 ≤ N ^ 2 := le_trans hN1 hN2
  have hnN : n ≤ N := by omega
  have haN : aLen ≤ N := by omega
  have hvN : v ≤ 2 * N := by omega
  have htN : t ≤ 2 * N + 1 := by omega
  have hvt_le : v * t ≤ 6 * N ^ 2 := by
    calc v * t ≤ (2 * N) * (3 * N) := Nat.mul_le_mul hvN (by omega)
      _ = 6 * N ^ 2 := by ring
  have hL1N : L + 1 ≤ 15 * N ^ 2 := by omega
  have hkN : k ≤ 30 * N ^ 3 := by
    calc k = v * (L + 1) := hk
      _ ≤ (2 * N) * (15 * N ^ 2) := Nat.mul_le_mul hvN hL1N
      _ = 30 * N ^ 3 := by ring
  have hwN : w ≤ 30 * N ^ 3 := le_trans hw hkN
  have hN6 : N ^ 3 * N ^ 3 = N ^ 6 := by ring
  have hN9 : N ^ 3 * N ^ 6 = N ^ 9 := by ring
  have hN3_le_9 : N ^ 3 ≤ N ^ 9 := by
    have : 1 ≤ N ^ 6 := Nat.one_le_pow 6 N hN1
    calc N ^ 3 = N ^ 3 * 1 := (Nat.mul_one _).symm
      _ ≤ N ^ 3 * N ^ 6 := Nat.mul_le_mul_left _ this
      _ = N ^ 9 := hN9
  have hN6_le_9 : N ^ 6 ≤ N ^ 9 := by
    have : 1 ≤ N ^ 3 := Nat.one_le_pow 3 N hN1
    calc N ^ 6 = 1 * N ^ 6 := (Nat.one_mul _).symm
      _ ≤ N ^ 3 * N ^ 6 := Nat.mul_le_mul_right _ this
      _ = N ^ 9 := hN9
  have hN2_le_9 : N ^ 2 ≤ N ^ 9 := le_trans hN3 hN3_le_9
  have hN1_le_9 : N ≤ N ^ 9 := le_trans hN2 hN2_le_9
  have h1_le_9 : 1 ≤ N ^ 9 := le_trans hN1 hN1_le_9
  have hNsq_le : (k + 1) ^ 2 ≤ 961 * N ^ 6 := by
    have hk1 : k + 1 ≤ 31 * N ^ 3 := by omega
    calc (k + 1) ^ 2 ≤ (31 * N ^ 3) ^ 2 := Nat.pow_le_pow_left hk1 2
      _ = 961 * N ^ 6 := by ring
  have hv1sq : (v + 1) ^ 2 ≤ 9 * N ^ 2 := by
    have : v + 1 ≤ 3 * N := by omega
    calc (v + 1) ^ 2 ≤ (3 * N) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 9 * N ^ 2 := by ring
  have hB1 : L + 1 + (n + n + v) * (L + 1) ≤ 75 * N ^ 3 := by
    have h1 : (n + n + v) * (L + 1) ≤ (4 * N) * (15 * N ^ 2) := Nat.mul_le_mul (by omega) hL1N
    have h1' : (4 * N) * (15 * N ^ 2) = 60 * N ^ 3 := by ring
    omega
  have hnL : n * (L + 1) ≤ 15 * N ^ 3 := by
    calc n * (L + 1) ≤ N * (15 * N ^ 2) := Nat.mul_le_mul hnN hL1N
      _ = 15 * N ^ 3 := by ring
  have hwfBound : wfLen ≤ 600000 * N ^ 9 := by
    have hterm1 : n * (L + 1) * (L + 1 + (n + n + v) * (L + 1)) * (2 * w) ≤ 100000 * N ^ 9 := by
      calc n * (L + 1) * (L + 1 + (n + n + v) * (L + 1)) * (2 * w)
          ≤ (15 * N ^ 3) * (75 * N ^ 3) * (60 * N ^ 3) :=
            Nat.mul_le_mul (Nat.mul_le_mul hnL hB1) (by omega)
        _ = 67500 * N ^ 9 := by ring
        _ ≤ 100000 * N ^ 9 := Nat.mul_le_mul_right _ (by decide)
    have hterm2 : n * (L + 1) * (L + 1 + n * (L + 1)) * (2 * w) ≤ 100000 * N ^ 9 := by
      have hB2 : L + 1 + n * (L + 1) ≤ 75 * N ^ 3 := by
        have h1 : n * (L + 1) ≤ (n + n + v) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
        omega
      calc n * (L + 1) * (L + 1 + n * (L + 1)) * (2 * w)
          ≤ (15 * N ^ 3) * (75 * N ^ 3) * (60 * N ^ 3) :=
            Nat.mul_le_mul (Nat.mul_le_mul hnL hB2) (by omega)
        _ = 67500 * N ^ 9 := by ring
        _ ≤ 100000 * N ^ 9 := Nat.mul_le_mul_right _ (by decide)
    omega
  have hBigW : 19 * w + 20 ≤ 600 * N ^ 3 := by omega
  have hLoop1 : n * ((L + 1) * ((L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
      12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 22) ≤ 1000000 * N ^ 9 := by
    have hinner : (L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
        12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50 ≤ 50000 * N ^ 6 := by
      have h1 : (L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) ≤ (75 * N ^ 3) * (600 * N ^ 3) :=
        Nat.mul_le_mul hB1 hBigW
      have h2 : (75 * N ^ 3) * (600 * N ^ 3) = 45000 * N ^ 6 := by ring
      have h3 : N ^ 3 ≤ N ^ 6 := by
        have : 1 ≤ N ^ 3 := Nat.one_le_pow 3 N hN1
        calc N ^ 3 = N ^ 3 * 1 := (Nat.mul_one _).symm
          _ ≤ N ^ 3 * N ^ 3 := Nat.mul_le_mul_left _ this
          _ = N ^ 6 := hN6
      have h4 : N ^ 2 ≤ N ^ 6 := le_trans hN3 h3
      have h5 : N ≤ N ^ 6 := le_trans hN2 h4
      have h6 : 1 ≤ N ^ 6 := le_trans hN1 h5
      omega
    have hmid : (L + 1) * ((L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
        12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50) ≤ (15 * N ^ 2) * (50000 * N ^ 6) :=
      Nat.mul_le_mul hL1N hinner
    have hmid2 : (15 * N ^ 2) * (50000 * N ^ 6) = 750000 * N ^ 8 := by ring
    have h16 : 16 * n + 22 ≤ 40 * N ^ 8 := by
      have : N ≤ N ^ 8 := by
        have h7 : 1 ≤ N ^ 7 := Nat.one_le_pow 7 N hN1
        calc N = N * 1 := (Nat.mul_one _).symm
          _ ≤ N * N ^ 7 := Nat.mul_le_mul_left _ h7
          _ = N ^ 8 := by ring
      have : 1 ≤ N ^ 8 := le_trans hN1 this
      omega
    calc n * ((L + 1) * ((L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
          12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 22)
        ≤ N * (750000 * N ^ 8 + 40 * N ^ 8) := Nat.mul_le_mul hnN (by omega)
      _ = 750040 * N ^ 9 := by ring
      _ ≤ 1000000 * N ^ 9 := Nat.mul_le_mul_right _ (by decide)
  have hLoop2 : n * ((L + 1) * ((L + 1 + n * (L + 1)) * (19 * w + 20) +
      12 * n + 7 * (L + 1) + 25 * w + 37) + 14 * (L + 1) + 12) ≤ 1000000 * N ^ 9 := by
    have hle : n * ((L + 1) * ((L + 1 + n * (L + 1)) * (19 * w + 20) +
        12 * n + 7 * (L + 1) + 25 * w + 37) + 14 * (L + 1) + 12) ≤
        n * ((L + 1) * ((L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
          12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 22) := by
      refine Nat.mul_le_mul_left n ?_
      have h1 : (L + 1 + n * (L + 1)) * (19 * w + 20) ≤ (L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
      have h2 := Nat.mul_le_mul_left (L + 1) (show (L + 1 + n * (L + 1)) * (19 * w + 20) +
          12 * n + 7 * (L + 1) + 25 * w + 37 + 14 ≤
          (L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
          12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50 by omega)
      have h3 : (L + 1) * ((L + 1 + n * (L + 1)) * (19 * w + 20) +
          12 * n + 7 * (L + 1) + 25 * w + 37 + 14) =
          (L + 1) * ((L + 1 + n * (L + 1)) * (19 * w + 20) +
            12 * n + 7 * (L + 1) + 25 * w + 37) + 14 * (L + 1) := by ring
      rw [h3] at h2
      have h4 : (L + 1) * ((L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
          12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50) + 12 ≤
          (L + 1) * ((L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
          12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 22 := by
        rw [Nat.add_assoc]
        exact Nat.add_le_add_left (le_trans (by decide : 12 ≤ 22) (Nat.le_add_left 22 (16 * n))) _
      exact le_trans (Nat.add_le_add_right h2 12) h4
    exact le_trans hle hLoop1
  have h16vt : 16 * v * t ≤ 96 * N ^ 2 := by
    calc 16 * v * t = 16 * (v * t) := by ring
      _ ≤ 16 * (6 * N ^ 2) := Nat.mul_le_mul_left 16 hvt_le
      _ = 96 * N ^ 2 := by ring
  have h10k : 10 * v * (L + 1) ≤ 300 * N ^ 3 := by
    calc 10 * v * (L + 1) = 10 * k := by rw [hk]; ring
      _ ≤ 10 * (30 * N ^ 3) := Nat.mul_le_mul_left 10 hkN
      _ = 300 * N ^ 3 := by ring
  omega

theorem write_spec_all (inp : List Bool) :
    let S0 := Function.update (fun _ : WK => ([] : List Bool)) wIn inp
    writeExec S0 = Function.update (fun _ : WK => ([] : List Bool)) wOut (writeFn inp) ∧
    1 + writeCost S0 ≤ (Polynomial.C 5000000000 * (Polynomial.X + 1) ^ 9).eval inp.length := by
  intro S0
  set n := (inp.takeWhile id).length
  set a := (inp.dropWhile id).tail
  set v := 2 * n
  set t := (v + 1).log2 + 1
  set L := 2 * (1 + v * t)
  set k := v * (L + 1)
  set w := k.bits.length
  have hL2 : 2 ≤ L := by omega
  have hA := wStageA_spec inp
  have hS1 : wStageAExec S0 =
      Function.update (Function.update (Function.update (Function.update S0 wIn a)
        wN (List.replicate n true)) wV (List.replicate v true)) wT (v + 1).bits := hA.1
  have hCA : wStageACost S0 ≤ 5 * (v + 1) ^ 2 + 30 * (v + 1) + 2 * inp.length + 30 := hA.2
  have hTlen : (v + 1).bits.length = t := bits_length_eq_log2 (v + 1) (Nat.succ_pos v)
  have hS1_empty : ∀ r : WK, r ≠ wT → r ≠ wV → r ≠ wN → r ≠ wIn → wStageAExec S0 r = [] := by
    intro r h1 h2 h3 h4
    rw [hS1]
    simp only [Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, S0]
  have hB := wStageB_spec (wStageAExec S0) v t
    (by rw [hS1]; simp only [Function.update_of_ne (by decide : wV ≠ wT), Function.update_self, List.length_replicate])
    (by rw [hS1]; simp only [Function.update_self, hTlen])
    (hS1_empty wL (by decide) (by decide) (by decide) (by decide))
    (hS1_empty wL1 (by decide) (by decide) (by decide) (by decide))
    (hS1_empty wLm1 (by decide) (by decide) (by decide) (by decide))
    (hS1_empty wTmp1 (by decide) (by decide) (by decide) (by decide))
    (hS1_empty wTmp2 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨lL, lL1, lLm1, hlL0, hlL10, hlLm10, hS2', hCB0⟩ := hB
  have hlL : lL.length = L := hlL0
  have hlL1 : lL1.length = L + 1 := hlL10
  have hlLm1 : lLm1.length = L - 1 := hlLm10
  have hCB : wStageBCost (wStageAExec S0) ≤ 16 * v * t + 14 * L + 14 * v + 3 * t + 20 := hCB0
  have hS2_empty : ∀ r : WK, r ≠ wLm1 → r ≠ wL1 → r ≠ wL → r ≠ wT → r ≠ wV → r ≠ wN → r ≠ wIn →
      wStageBExec (wStageAExec S0) r = [] := by
    intro r h1 h2 h3 h4 h5 h6 h7
    rw [hS2']
    simp only [Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4]
    exact hS1_empty r h4 h5 h6 h7
  have hC := wStageC_spec (wStageBExec (wStageAExec S0)) n v L
    (by rw [hS2', hS1]; simp only [Function.update_of_ne (by decide : wN ≠ wLm1),
      Function.update_of_ne (by decide : wN ≠ wL1), Function.update_of_ne (by decide : wN ≠ wL),
      Function.update_of_ne (by decide : wN ≠ wT), Function.update_of_ne (by decide : wN ≠ wV),
      Function.update_self, List.length_replicate])
    (by rw [hS2', hS1]; simp only [Function.update_of_ne (by decide : wV ≠ wLm1),
      Function.update_of_ne (by decide : wV ≠ wL1), Function.update_of_ne (by decide : wV ≠ wL),
      Function.update_of_ne (by decide : wV ≠ wT), Function.update_self, List.length_replicate])
    (by rw [hS2']; simp only [Function.update_of_ne (by decide : wL1 ≠ wLm1), Function.update_self, hlL1])
    (by rw [hS2']; simp only [Function.update_of_ne (by decide : wT ≠ wLm1),
      Function.update_of_ne (by decide : wT ≠ wL1), Function.update_of_ne (by decide : wT ≠ wL), Function.update_self])
    (hS2_empty wBlk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hS2_empty wOutRev (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hS2_empty wX (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hS2_empty wRemLeft (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hS2_empty wRemAll (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hS2_empty wTmp1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hS2_empty wTmp2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hS3' : wStageCExec (wStageBExec (wStageAExec S0)) =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (wStageBExec (wStageAExec S0)) wV [])
        wOutRev (false :: List.replicate k true)) wX (fieldBits w 0))
        wRemLeft (wStageBExec (wStageAExec S0) wN)) wRemAll (wStageBExec (wStageAExec S0) wV) := hC.1
  have hCC : wStageCCost (wStageBExec (wStageAExec S0)) ≤
      5 * (k + 1) ^ 2 + 30 * (k + 1) + 10 * v * (L + 1) + 25 * v + 7 * n + 20 := hC.2
  set S3 := wStageCExec (wStageBExec (wStageAExec S0))
  have hS3 : S3 =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update S0 wIn a)
          wN (List.replicate n true)) wL lL) wL1 lL1) wLm1 lLm1)
        wOutRev (false :: List.replicate k true)) wX (fieldBits w 0))
        wRemLeft (List.replicate n true)) wRemAll (List.replicate v true) := by
    rw [hS3', hS2', hS1]
    funext j
    by_cases j1 : j = wRemAll; · subst j1; simp [Fin.ext_iff]
    by_cases j2 : j = wRemLeft; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = wX; · subst j3; simp [Fin.ext_iff]
    by_cases j4 : j = wOutRev; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = wV; · subst j5; simp [S0, Fin.ext_iff]
    by_cases j6 : j = wLm1; · subst j6; simp [Fin.ext_iff]
    by_cases j7 : j = wL1; · subst j7; simp [Fin.ext_iff]
    by_cases j8 : j = wL; · subst j8; simp [Fin.ext_iff]
    by_cases j9 : j = wT; · subst j9; simp [S0, Fin.ext_iff]
    by_cases j10 : j = wN; · subst j10; simp [Fin.ext_iff]
    by_cases j11 : j = wIn; · subst j11; simp [Fin.ext_iff]
    simp [S0, Fin.ext_iff, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11]

  have hS3_empty : ∀ r : WK, r ≠ wRemAll → r ≠ wRemLeft → r ≠ wX → r ≠ wOutRev →
      r ≠ wLm1 → r ≠ wL1 → r ≠ wL → r ≠ wN → r ≠ wIn → S3 r = [] := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [hS3]
    simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
      Function.update_of_ne h7, Function.update_of_ne h8, Function.update_of_ne h9, S0]
  have hS3_N : S3 wN = List.replicate n true := by
    rw [hS3]; simp only [Function.update_of_ne (by decide : wN ≠ wRemAll),
      Function.update_of_ne (by decide : wN ≠ wRemLeft), Function.update_of_ne (by decide : wN ≠ wX),
      Function.update_of_ne (by decide : wN ≠ wOutRev), Function.update_of_ne (by decide : wN ≠ wLm1),
      Function.update_of_ne (by decide : wN ≠ wL1), Function.update_of_ne (by decide : wN ≠ wL), Function.update_self]
  have hS3_L : S3 wL = lL := by
    rw [hS3]; simp only [Function.update_of_ne (by decide : wL ≠ wRemAll),
      Function.update_of_ne (by decide : wL ≠ wRemLeft), Function.update_of_ne (by decide : wL ≠ wX),
      Function.update_of_ne (by decide : wL ≠ wOutRev), Function.update_of_ne (by decide : wL ≠ wLm1),
      Function.update_of_ne (by decide : wL ≠ wL1), Function.update_self]
  have hS3_L1 : S3 wL1 = lL1 := by
    rw [hS3]; simp only [Function.update_of_ne (by decide : wL1 ≠ wRemAll),
      Function.update_of_ne (by decide : wL1 ≠ wRemLeft), Function.update_of_ne (by decide : wL1 ≠ wX),
      Function.update_of_ne (by decide : wL1 ≠ wOutRev), Function.update_of_ne (by decide : wL1 ≠ wLm1), Function.update_self]
  have hS3_Lm1 : S3 wLm1 = lLm1 := by
    rw [hS3]; simp only [Function.update_of_ne (by decide : wLm1 ≠ wRemAll),
      Function.update_of_ne (by decide : wLm1 ≠ wRemLeft), Function.update_of_ne (by decide : wLm1 ≠ wX),
      Function.update_of_ne (by decide : wLm1 ≠ wOutRev), Function.update_self]
  have hS3_RL : S3 wRemLeft = List.replicate n true := by
    rw [hS3]; simp only [Function.update_of_ne (by decide : wRemLeft ≠ wRemAll), Function.update_self]
  have hS3_RA : S3 wRemAll = List.replicate v true := by
    rw [hS3]; simp only [Function.update_self]
  have hS3_X : S3 wX = fieldBits w 0 := by
    rw [hS3]; simp only [Function.update_of_ne (by decide : wX ≠ wRemAll),
      Function.update_of_ne (by decide : wX ≠ wRemLeft), Function.update_self]
  set S4 := copyExec wN wNloop wTmp1 S3
  have hD1 : S4 = Function.update S3 wNloop (List.replicate n true) := by
    show copyExec wN wNloop wTmp1 S3 = _
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S3
      (hS3_empty wTmp1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [hS3_N, hS3_empty wNloop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        List.append_nil]
  have hD1l : S4 wNloop = List.replicate n true := by rw [hD1]; simp only [Function.update_self]
  have hS4_ne : ∀ r : WK, r ≠ wNloop → S4 r = S3 r := fun r hr => by rw [hD1, Function.update_of_ne hr]
  have hS40_ne : ∀ r : WK, r ≠ wNloop → Function.update S4 wNloop [] r = S3 r := fun r hr => by
    rw [Function.update_of_ne hr, hS4_ne r hr]
  have hLres1 := leftFold_spec n L w hL2 (List.replicate n true) 0 v (Function.update S4 wNloop []) (by simp [v]; omega)
    (by rw [hS40_ne wN (by decide), hS3_N, List.length_replicate])
    (by rw [hS40_ne wL (by decide), hS3_L, hlL])
    (by rw [hS40_ne wL1 (by decide), hS3_L1, hlL1])
    (by rw [hS40_ne wLm1 (by decide), hS3_Lm1, hlLm1])
    (by rw [hS40_ne wRemLeft (by decide), hS3_RL])
    (by rw [hS40_ne wRemAll (by decide), hS3_RA, List.length_replicate])
    (by rw [hS40_ne wX (by decide), hS3_X])
    (by rw [hS40_ne wY (by decide)]; exact hS3_empty wY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS40_ne wRemR (by decide)]; exact hS3_empty wRemR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS40_ne wRow (by decide)]; exact hS3_empty wRow (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS40_ne wCnt (by decide)]; exact hS3_empty wCnt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS40_ne wBlk (by decide)]; exact hS3_empty wBlk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS40_ne wRxLoop (by decide)]; exact hS3_empty wRxLoop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS40_ne wTmp1 (by decide)]; exact hS3_empty wTmp1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS40_ne wTmp2 (by decide)]; exact hS3_empty wTmp2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hLres2 := leftFold_spec n L w hL2 (List.replicate n true) 0 v S4 (by simp [v]; omega)
    (by rw [hS4_ne wN (by decide), hS3_N, List.length_replicate])
    (by rw [hS4_ne wL (by decide), hS3_L, hlL])
    (by rw [hS4_ne wL1 (by decide), hS3_L1, hlL1])
    (by rw [hS4_ne wLm1 (by decide), hS3_Lm1, hlLm1])
    (by rw [hS4_ne wRemLeft (by decide), hS3_RL])
    (by rw [hS4_ne wRemAll (by decide), hS3_RA, List.length_replicate])
    (by rw [hS4_ne wX (by decide), hS3_X])
    (by rw [hS4_ne wY (by decide)]; exact hS3_empty wY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS4_ne wRemR (by decide)]; exact hS3_empty wRemR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS4_ne wRow (by decide)]; exact hS3_empty wRow (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS4_ne wCnt (by decide)]; exact hS3_empty wCnt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS4_ne wBlk (by decide)]; exact hS3_empty wBlk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS4_ne wRxLoop (by decide)]; exact hS3_empty wRxLoop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS4_ne wTmp1 (by decide)]; exact hS3_empty wTmp1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS4_ne wTmp2 (by decide)]; exact hS3_empty wTmp2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  set S5 := (S4 wNloop).foldl (fun U _ => leftBlockExec U) (Function.update S4 wNloop [])
  have hD2 : S5 =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update S0 wIn (a.drop (n * n)))
          wN (List.replicate n true)) wL lL) wL1 lL1) wLm1 lLm1)
        wOutRev ((emitLeftBlocks w L n n 0 v a).reverse ++ false :: List.replicate k true))
        wX (fieldBits w (n * (L + 1)))) wRemAll (List.replicate n true) := by
    show (S4 wNloop).foldl (fun U _ => leftBlockExec U) (Function.update S4 wNloop []) = _
    rw [hD1l, hLres1.1, hD1, hS3]
    have hdropV : (List.replicate v true).drop n = List.replicate n true := by
      simp [v, show 2 * n - n = n by omega]
    funext j
    by_cases j1 : j = wRemAll; · subst j1; simp [Fin.ext_iff, hdropV]
    by_cases j2 : j = wX; · subst j2; simp [Fin.ext_iff]
    by_cases j3 : j = wOutRev; · subst j3; simp [Fin.ext_iff]
    by_cases j4 : j = wLm1; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = wL1; · subst j5; simp [Fin.ext_iff]
    by_cases j6 : j = wL; · subst j6; simp [Fin.ext_iff]
    by_cases j7 : j = wN; · subst j7; simp [Fin.ext_iff]
    by_cases j8 : j = wIn; · subst j8; simp [Fin.ext_iff]
    by_cases j9 : j = wRemLeft; · subst j9; simp [S0, Fin.ext_iff]
    by_cases j10 : j = wNloop; · subst j10; simp [S0, Fin.ext_iff]
    simp [S0, Fin.ext_iff, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10]
  have hS5_empty : ∀ r : WK, r ≠ wRemAll → r ≠ wX → r ≠ wOutRev →
      r ≠ wLm1 → r ≠ wL1 → r ≠ wL → r ≠ wN → r ≠ wIn → S5 r = [] := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8
    rw [hD2]
    simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
      Function.update_of_ne h7, Function.update_of_ne h8, S0]
  have hS5_N : S5 wN = List.replicate n true := by
    rw [hD2]; simp only [Function.update_of_ne (by decide : wN ≠ wRemAll),
      Function.update_of_ne (by decide : wN ≠ wX), Function.update_of_ne (by decide : wN ≠ wOutRev),
      Function.update_of_ne (by decide : wN ≠ wLm1), Function.update_of_ne (by decide : wN ≠ wL1),
      Function.update_of_ne (by decide : wN ≠ wL), Function.update_self]
  have hS5_L1 : S5 wL1 = lL1 := by
    rw [hD2]; simp only [Function.update_of_ne (by decide : wL1 ≠ wRemAll),
      Function.update_of_ne (by decide : wL1 ≠ wX), Function.update_of_ne (by decide : wL1 ≠ wOutRev),
      Function.update_of_ne (by decide : wL1 ≠ wLm1), Function.update_self]
  have hS5_RA : S5 wRemAll = List.replicate n true := by rw [hD2]; simp only [Function.update_self]
  have hS5_X : S5 wX = fieldBits w (n * (L + 1)) := by
    rw [hD2]; simp only [Function.update_of_ne (by decide : wX ≠ wRemAll), Function.update_self]
  set S6 := copyExec wN wNloop wTmp1 S5
  have hD3 : S6 = Function.update S5 wNloop (List.replicate n true) := by
    show copyExec wN wNloop wTmp1 S5 = _
    rw [copyExec_of_empty (by decide) (by decide) (by decide) S5
      (hS5_empty wTmp1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))]
    rw [hS5_N, hS5_empty wNloop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        List.append_nil]
  have hD3l : S6 wNloop = List.replicate n true := by rw [hD3]; simp only [Function.update_self]
  have hS6_ne : ∀ r : WK, r ≠ wNloop → S6 r = S5 r := fun r hr => by rw [hD3, Function.update_of_ne hr]
  have hS60_ne : ∀ r : WK, r ≠ wNloop → Function.update S6 wNloop [] r = S5 r := fun r hr => by
    rw [Function.update_of_ne hr, hS6_ne r hr]
  have hRres1 := rightFold_spec L w (List.replicate n true) (n * (L + 1)) (Function.update S6 wNloop [])
    (by rw [hS60_ne wL1 (by decide), hS5_L1, hlL1])
    (by rw [hS60_ne wRemAll (by decide), hS5_RA])
    (by rw [hS60_ne wX (by decide), hS5_X])
    (by rw [hS60_ne wY (by decide)]; exact hS5_empty wY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS60_ne wRemR (by decide)]; exact hS5_empty wRemR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS60_ne wCnt (by decide)]; exact hS5_empty wCnt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS60_ne wBlk (by decide)]; exact hS5_empty wBlk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS60_ne wRxLoop (by decide)]; exact hS5_empty wRxLoop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS60_ne wTmp1 (by decide)]; exact hS5_empty wTmp1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hRres2 := rightFold_spec L w (List.replicate n true) (n * (L + 1)) S6
    (by rw [hS6_ne wL1 (by decide), hS5_L1, hlL1])
    (by rw [hS6_ne wRemAll (by decide), hS5_RA])
    (by rw [hS6_ne wX (by decide), hS5_X])
    (by rw [hS6_ne wY (by decide)]; exact hS5_empty wY (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS6_ne wRemR (by decide)]; exact hS5_empty wRemR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS6_ne wCnt (by decide)]; exact hS5_empty wCnt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS6_ne wBlk (by decide)]; exact hS5_empty wBlk (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS6_ne wRxLoop (by decide)]; exact hS5_empty wRxLoop (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by rw [hS6_ne wTmp1 (by decide)]; exact hS5_empty wTmp1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  set S7 := (S6 wNloop).foldl (fun U _ => rightBlockExec U) (Function.update S6 wNloop [])
  have hD4 : S7 =
      Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update S0 wIn (a.drop (n * n)))
          wN (List.replicate n true)) wL lL) wL1 lL1) wLm1 lLm1)
        wOutRev (writeFn inp).reverse) wX (fieldBits w k) := by
    show (S6 wNloop).foldl (fun U _ => rightBlockExec U) (Function.update S6 wNloop []) = _
    rw [hD3l, hRres1.1, hD3, hD2]
    have hrev : (emitRightBlocks w L n (n * (L + 1)) n).reverse ++
        ((emitLeftBlocks w L n n 0 v a).reverse ++ false :: List.replicate k true) =
        (writeFn inp).reverse := by
      change (emitRightBlocks w L n (n * (L + 1)) n).reverse ++
        ((emitLeftBlocks w L n n 0 v a).reverse ++ false :: List.replicate k true) =
        (List.replicate k true ++ [false] ++ emitLeftBlocks w L n n 0 v a ++
          emitRightBlocks w L n (n * (L + 1)) n).reverse
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.reverse_replicate, List.nil_append, List.append_assoc, List.singleton_append]
    funext j
    by_cases j1 : j = wX
    · subst j1; simp [Fin.ext_iff, show n * (L + 1) + n * (L + 1) = k by simp [k, v]; ring]
    by_cases j2 : j = wOutRev; · subst j2; simp [Fin.ext_iff, hrev]
    by_cases j3 : j = wLm1; · subst j3; simp [Fin.ext_iff]
    by_cases j4 : j = wL1; · subst j4; simp [Fin.ext_iff]
    by_cases j5 : j = wL; · subst j5; simp [Fin.ext_iff]
    by_cases j6 : j = wN; · subst j6; simp [Fin.ext_iff]
    by_cases j7 : j = wIn; · subst j7; simp [Fin.ext_iff]
    by_cases j8 : j = wRemAll; · subst j8; simp [S0, Fin.ext_iff]
    by_cases j9 : j = wNloop; · subst j9; simp [S0, Fin.ext_iff]
    simp [S0, Fin.ext_iff, j1, j2, j3, j4, j5, j6, j7, j8, j9]
  refine ⟨?_, ?_⟩
  · simp only [writeExec]
    change revMoveExec wOutRev wOut (clearExec wX (clearExec wLm1 (clearExec wL1 (clearExec wL (clearExec wN (clearExec wIn S7)))))) = _
    rw [hD4]
    funext j; simp only [clearExec, revMoveExec]
    by_cases j1 : j = wOut; · subst j1; simp [S0, Fin.ext_iff]
    by_cases j2 : j = wOutRev; · subst j2; simp [S0, Fin.ext_iff]
    by_cases j3 : j = wX; · subst j3; simp [S0, Fin.ext_iff]
    by_cases j4 : j = wLm1; · subst j4; simp [S0, Fin.ext_iff]
    by_cases j5 : j = wL1; · subst j5; simp [S0, Fin.ext_iff]
    by_cases j6 : j = wL; · subst j6; simp [S0, Fin.ext_iff]
    by_cases j7 : j = wN; · subst j7; simp [S0, Fin.ext_iff]
    by_cases j8 : j = wIn; · subst j8; simp [S0, Fin.ext_iff]
    simp [S0, Fin.ext_iff, j1, j2, j3, j4, j5, j6, j7, j8]
  · simp only [writeCost, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    change 1 + (wStageDCost S3 + (wStageCCost (wStageBExec (wStageAExec S0)) +
      (wStageBCost (wStageAExec S0) + wStageACost S0))) ≤ _
    have hCD : wStageDCost S3 ≤
        3 * (writeFn inp).length + 3 * w + 3 * L + 3 * (L + 1) + 3 * (L - 1) + 17 * n + 3 * a.length +
          n * ((L + 1) * ((L + 1 + (n + n + v) * (L + 1)) * (19 * w + 20) +
            12 * (n + n + v) + 21 * (L + 1) + 25 * w + 50) + 16 * n + 22) +
          n * ((L + 1) * ((L + 1 + n * (L + 1)) * (19 * w + 20) +
            12 * n + 7 * (L + 1) + 25 * w + 37) + 14 * (L + 1) + 12) + 30 := by
      change (3 * (clearExec wX (clearExec wLm1 (clearExec wL1 (clearExec wL (clearExec wN (clearExec wIn S7))))) wOutRev).length + 1) +
        ((3 * (clearExec wLm1 (clearExec wL1 (clearExec wL (clearExec wN (clearExec wIn S7)))) wX).length + 1) +
          ((3 * (clearExec wL1 (clearExec wL (clearExec wN (clearExec wIn S7))) wLm1).length + 1) +
            ((3 * (clearExec wL (clearExec wN (clearExec wIn S7)) wL1).length + 1) +
              ((3 * (clearExec wN (clearExec wIn S7) wL).length + 1) +
                ((3 * (clearExec wIn S7 wN).length + 1) +
                  ((3 * (S7 wIn).length + 1) +
                    (forEachCost wNloop (fun _ => rightBlockExec) (fun _ => rightBlockCost) (S6 wNloop) S6 +
                      ((7 * (S5 wN).length + 4 * (S5 wTmp1).length + 2) +
                        (forEachCost wNloop (fun _ => leftBlockExec) (fun _ => leftBlockCost) (S4 wNloop) S4 +
                          (7 * (S3 wN).length + 4 * (S3 wTmp1).length + 2)))))))))) ≤ _
      have hcL := hLres2.2
      have hcR := hRres2.2
      simp only [List.length_replicate] at hcL hcR
      have h7Out : (clearExec wX (clearExec wLm1 (clearExec wL1 (clearExec wL (clearExec wN (clearExec wIn S7))))) wOutRev).length =
          (writeFn inp).length := by
        rw [hD4]; simp only [clearExec, Function.update_of_ne (by decide : wOutRev ≠ wX),
          Function.update_of_ne (by decide : wOutRev ≠ wLm1), Function.update_of_ne (by decide : wOutRev ≠ wL1),
          Function.update_of_ne (by decide : wOutRev ≠ wL), Function.update_of_ne (by decide : wOutRev ≠ wN),
          Function.update_of_ne (by decide : wOutRev ≠ wIn), Function.update_self, List.length_reverse]
      have h7X : (clearExec wLm1 (clearExec wL1 (clearExec wL (clearExec wN (clearExec wIn S7)))) wX).length = w := by
        rw [hD4]; simp only [clearExec, Function.update_of_ne (by decide : wX ≠ wLm1),
          Function.update_of_ne (by decide : wX ≠ wL1), Function.update_of_ne (by decide : wX ≠ wL),
          Function.update_of_ne (by decide : wX ≠ wN), Function.update_of_ne (by decide : wX ≠ wIn),
          Function.update_self, fieldBits_length]
      have h7Lm1 : (clearExec wL1 (clearExec wL (clearExec wN (clearExec wIn S7))) wLm1).length = L - 1 := by
        rw [hD4]; simp only [clearExec, Function.update_of_ne (by decide : wLm1 ≠ wL1),
          Function.update_of_ne (by decide : wLm1 ≠ wL), Function.update_of_ne (by decide : wLm1 ≠ wN),
          Function.update_of_ne (by decide : wLm1 ≠ wIn), Function.update_of_ne (by decide : wLm1 ≠ wX),
          Function.update_of_ne (by decide : wLm1 ≠ wOutRev), Function.update_self, hlLm1]
      have h7L1 : (clearExec wL (clearExec wN (clearExec wIn S7)) wL1).length = L + 1 := by
        rw [hD4]; simp only [clearExec, Function.update_of_ne (by decide : wL1 ≠ wL),
          Function.update_of_ne (by decide : wL1 ≠ wN), Function.update_of_ne (by decide : wL1 ≠ wIn),
          Function.update_of_ne (by decide : wL1 ≠ wX), Function.update_of_ne (by decide : wL1 ≠ wOutRev),
          Function.update_of_ne (by decide : wL1 ≠ wLm1), Function.update_self, hlL1]
      have h7L : (clearExec wN (clearExec wIn S7) wL).length = L := by
        rw [hD4]; simp only [clearExec, Function.update_of_ne (by decide : wL ≠ wN),
          Function.update_of_ne (by decide : wL ≠ wIn), Function.update_of_ne (by decide : wL ≠ wX),
          Function.update_of_ne (by decide : wL ≠ wOutRev), Function.update_of_ne (by decide : wL ≠ wLm1),
          Function.update_of_ne (by decide : wL ≠ wL1), Function.update_self, hlL]
      have h7N : (clearExec wIn S7 wN).length = n := by
        rw [hD4]; simp only [clearExec, Function.update_of_ne (by decide : wN ≠ wIn),
          Function.update_of_ne (by decide : wN ≠ wX), Function.update_of_ne (by decide : wN ≠ wOutRev),
          Function.update_of_ne (by decide : wN ≠ wLm1), Function.update_of_ne (by decide : wN ≠ wL1),
          Function.update_of_ne (by decide : wN ≠ wL), Function.update_self, List.length_replicate]
      have h7In : (S7 wIn).length = a.length - n * n := by
        rw [hD4]; simp only [Function.update_of_ne (by decide : wIn ≠ wX),
          Function.update_of_ne (by decide : wIn ≠ wOutRev), Function.update_of_ne (by decide : wIn ≠ wLm1),
          Function.update_of_ne (by decide : wIn ≠ wL1), Function.update_of_ne (by decide : wIn ≠ wL),
          Function.update_of_ne (by decide : wIn ≠ wN), Function.update_self, List.length_drop]
      have h5N : (S5 wN).length = n := by rw [hS5_N, List.length_replicate]
      have h5t : (S5 wTmp1).length = 0 := by
        rw [hS5_empty wTmp1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
      have h3N : (S3 wN).length = n := by rw [hS3_N, List.length_replicate]
      have h3t : (S3 wTmp1).length = 0 := by
        rw [hS3_empty wTmp1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
      rw [h7Out, h7X, h7Lm1, h7L1, h7L, h7N, h7In, h5N, h5t, h3N, h3t, hD3l, hD1l]
      have hdrop_le : a.length - n * n ≤ a.length := Nat.sub_le _ _
      omega
    exact write_poly_bound inp.length n a.length v t L k w (writeFn inp).length
      (wStageACost S0) (wStageBCost (wStageAExec S0))
      (wStageCCost (wStageBExec (wStageAExec S0))) (wStageDCost S3)
      (List.takeWhile_prefix _).length_le
      (by have h1 := (List.dropWhile_suffix (l := inp) id).length_le; simp only [a, List.length_tail]; omega)
      rfl
      (by have := bits_length_le (v + 1); rw [bits_length_eq_log2 (v + 1) (Nat.succ_pos v)] at this; exact this)
      rfl rfl (bits_length_le k)
      (by
        change (List.replicate k true ++ [false] ++ emitLeftBlocks w L n n 0 v a ++
          emitRightBlocks w L n (n * (L + 1)) n).length ≤ _
        simp only [List.length_append, List.length_replicate, List.length_singleton]
        have hl1 := emitLeftBlocks_len_le w L n n 0 v a
        have hl2 := emitRightBlocks_len_le w L n (n * (L + 1)) n
        omega)
      hCA hCB hCC hCD

theorem write_fast :
    ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) writeFn,
      ∀ i, Finite (M.tm.Γ i) :=
  psb_to_polyTime wIn wOut psb_write writeFn (Polynomial.C 5000000000 * (Polynomial.X + 1) ^ 9)
    (fun x => (write_spec_all x).1) (fun x => (write_spec_all x).2)


theorem list_range_add (a b : ℕ) :
    List.range (a + b) = List.range a ++ (List.range b).map (fun d => a + d) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, List.range_succ, List.map_append, List.map_cons,
        List.map_nil, ih, List.append_assoc]

theorem list_range_mul (m d : ℕ) :
    List.range (m * d) = (List.range m).flatMap (fun q => (List.range d).map (fun r => q * d + r)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, list_range_add, ih, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]

theorem list_range_mul_shift (base m d : ℕ) :
    (List.range (m * d)).map (fun z => base + z) =
      (List.range m).flatMap (fun q => (List.range d).map (fun r => base + q * d + r)) := by
  rw [list_range_mul, List.map_flatMap]
  apply List.flatMap_congr
  intro q _
  rw [List.map_map]
  apply List.map_congr_left
  intro r _
  dsimp only [Function.comp_apply]
  omega

theorem list_flatMap_flatMap {α β γ : Type} (l : List α) (f : α → List β) (g : β → List γ) :
    (l.flatMap f).flatMap g = l.flatMap (fun x => (f x).flatMap g) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.flatMap_append, ih]

theorem filter_map_eq_all {α : Type} (l : List α) (p : α → Bool) (hp : ∀ a ∈ l, p a = true) :
    l.filter p = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, hp a List.mem_cons_self, ↓reduceIte]
    rw [ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))]

theorem filter_map_eq_nil {α : Type} (l : List α) (p : α → Bool) (hp : ∀ a ∈ l, p a = false) :
    l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, hp a List.mem_cons_self, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))

theorem cells_map_drop (n : ℕ) (A : Fin n → Fin n → Bool) :
    ∀ (m : ℕ), m ≤ n →
      let cells := (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))
      let a := cells.map (fun z => A z.1 z.2)
      a.drop (m * n) =
        ((List.finRange n).drop m).flatMap (fun i => (List.finRange n).map (fun j => A i j)) := by
  intro m hm cells a
  have ha : a = (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => A i j)) := by
    simp only [a, cells, List.map_flatMap]
    apply List.flatMap_congr; intro i _; rw [List.map_map]; rfl
  rw [ha]
  have hdrop_add : ∀ (a b : ℕ) (xs : List Bool), xs.drop (a + b) = (xs.drop a).drop b := by
    intro a b xs
    induction a generalizing xs with
    | zero => simp
    | succ a ih =>
      cases xs with
      | nil => simp
      | cons _ xs => rw [Nat.succ_add, List.drop_succ_cons, List.drop_succ_cons, ih]
  have hdrop_app : ∀ (xs ys : List Bool), (xs ++ ys).drop xs.length = ys := by
    intro xs ys
    induction xs with
    | nil => simp
    | cons _ _ ih => simp [ih]
  have hlen : ∀ (l : List (Fin n)),
      (l.flatMap (fun i => (List.finRange n).map (fun j => A i j))).drop (m * n) =
        (l.drop m).flatMap (fun i => (List.finRange n).map (fun j => A i j)) := by
    intro l
    induction m generalizing l with
    | zero => simp
    | succ m ih =>
      cases l with
      | nil => simp
      | cons i l =>
        rw [Nat.succ_mul, Nat.add_comm, List.flatMap_cons, hdrop_add]
        have hl : ((List.finRange n).map (fun j => A i j)).length = n := by simp
        have h1 : (((List.finRange n).map (fun j => A i j)) ++
            (l.flatMap (fun i => (List.finRange n).map (fun j => A i j)))).drop n =
            l.flatMap (fun i => (List.finRange n).map (fun j => A i j)) := by
          simpa [hl] using hdrop_app ((List.finRange n).map (fun j => A i j))
            (l.flatMap (fun i => (List.finRange n).map (fun j => A i j)))
        rw [h1, List.drop_succ_cons]
        exact ih (by omega) l
  exact hlen (List.finRange n)

theorem writeFn_on_valid (n : ℕ) (hn : 0 < n) (A : Fin n → Fin n → Bool) :
    let v := 2 * n
    let L := 2 * (1 + v * ((v + 1).log2 + 1))
    let k := v * (L + 1)
    let cells := (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i, j)))
    let base := (cells.filter (fun z => A z.1 z.2)).map (fun z =>
      (z.1.val * (L + 1), (n + z.2.val) * (L + 1)))
    let good := fun (x y : Nat) => (x, y) ∈ base ∨ (y = x + 1 ∧ x / (L + 1) = y / (L + 1))
    let ban := (List.range k).flatMap (fun x => ((List.range k).filter (fun y =>
      decide (x < y ∧ ¬ good x y))).map (fun y => (x, y)))
    let header := fun m : Nat => List.replicate m true ++ [false]
    let field := fun (m z : Nat) => (List.range (m.log2 + 1)).map (fun h => z.testBit h)
    writeFn (header n ++ cells.map (fun z => A z.1 z.2)) =
      header k ++ ban.flatMap (fun e => field k e.1 ++ field k e.2) := by
  intro v L k cells base good ban header field
  set a := cells.map (fun z => A z.1 z.2)
  have htw : (header n ++ a).takeWhile id = List.replicate n true := by
    simp only [header, List.append_assoc, List.singleton_append]
    induction n with | zero => rfl | succ m ih => simp [List.replicate_succ, ih]
  have hdw : ((header n ++ a).dropWhile id).tail = a := by
    simp only [header, List.append_assoc, List.singleton_append]
    induction n with | zero => rfl | succ m ih => simp [List.replicate_succ, ih]
  have hk_pos : 0 < k := Nat.mul_pos (by omega) (by omega)
  have hw_eq : k.bits.length = k.log2 + 1 := bits_length_eq_log2 k hk_pos
  have hL2 : 2 ≤ L := by omega
  set w := k.log2 + 1
  have hfield : ∀ z, field k z = fieldBits w z := fun _ => rfl
  simp only [writeFn, htw, hdw, List.length_replicate]
  change header k ++ emitLeftBlocks k.bits.length L n n 0 v a ++ emitRightBlocks k.bits.length L n (n * (L + 1)) n =
    header k ++ ban.flatMap (fun e => fieldBits w e.1 ++ fieldBits w e.2)
  rw [hw_eq]
  rw [List.append_assoc]
  congr 1

  let banRow : ℕ → List Bool := fun x =>
    ((List.range k).filter (fun y => decide (x < y ∧ ¬ good x y))).flatMap (fun y => emitPairBits w x y)
  have hban_flat : ban.flatMap (fun e => fieldBits w e.1 ++ fieldBits w e.2) =
      (List.range k).flatMap banRow := by
    simp only [ban, list_flatMap_flatMap]
    apply List.flatMap_congr; intro x _
    rw [List.flatMap_map]; rfl
  rw [hban_flat]

  have hbase_iff : ∀ x y : ℕ, (x, y) ∈ base ↔
      ∃ (i j : Fin n), A i j = true ∧ x = i.val * (L + 1) ∧ y = (n + j.val) * (L + 1) := by
    intro x y
    simp only [base, cells, List.mem_map, List.mem_filter, List.mem_flatMap, List.mem_finRange, true_and]
    constructor
    · rintro ⟨⟨i, j⟩, ⟨⟨i', j', h1⟩, hA⟩, h2⟩
      rcases Prod.mk.inj h1 with ⟨rfl, rfl⟩
      rcases Prod.mk.inj h2 with ⟨h21, h22⟩
      exact ⟨i', j', hA, h21.symm, h22.symm⟩
    · rintro ⟨i, j, hA, rfl, rfl⟩
      exact ⟨(i, j), ⟨⟨i, j, rfl⟩, hA⟩, rfl⟩
  have hdiv_blk : ∀ (q r : ℕ), r < L + 1 → (q * (L + 1) + r) / (L + 1) = q := by
    intro q r hr
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (Nat.succ_pos L),
        Nat.div_eq_of_lt hr, Nat.zero_add]
  have hrail_iff : ∀ (qx rx y : ℕ), rx < L + 1 →
      let x := qx * (L + 1) + rx
      (y = x + 1 ∧ x / (L + 1) = y / (L + 1)) ↔ (y = x + 1 ∧ rx < L) := by
    intro qx rx y hrx x
    constructor
    · rintro ⟨rfl, hdiv⟩
      refine ⟨rfl, ?_⟩
      by_contra hge
      have hrxL : rx = L := by omega
      have h1 : x / (L + 1) = qx := hdiv_blk qx rx hrx
      have h2 : (x + 1) / (L + 1) = qx + 1 := by
        have hx1 : x + 1 = (qx + 1) * (L + 1) := by simp only [x, hrxL]; ring
        rw [hx1, Nat.mul_div_cancel _ (Nat.succ_pos L)]
      omega
    · rintro ⟨rfl, hrL⟩
      refine ⟨rfl, ?_⟩
      rw [hdiv_blk qx rx hrx]
      have hx1 : x + 1 = qx * (L + 1) + (rx + 1) := by simp only [x]; omega
      rw [hx1, hdiv_blk qx (rx + 1) (by omega)]
  have hgood_noBase : ∀ (qx rx y : ℕ), rx < L + 1 → (0 < rx ∨ n ≤ qx) →
      (good (qx * (L + 1) + rx) y ↔ (y = qx * (L + 1) + rx + 1 ∧ rx < L)) := by
    intro qx rx y hrx hor
    set x := qx * (L + 1) + rx
    simp only [good]
    have hnb : (x, y) ∉ base := by
      intro hb
      rcases (hbase_iff x y).mp hb with ⟨i, j, -, hxi, -⟩
      have hmod : x % (L + 1) = rx := by
        rw [show x = rx + (L + 1) * qx by simp only [x]; ring,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrx]
      have hmod2 : x % (L + 1) = 0 := by rw [hxi, Nat.mul_mod_left]
      have hrx0 : rx = 0 := by omega
      have hqeq : qx = i.val := by
        have := hdiv_blk qx rx hrx
        change x / (L + 1) = qx at this
        rw [hxi, Nat.mul_div_cancel _ (Nat.succ_pos L)] at this
        exact this.symm
      rcases hor with hpos | hge
      · omega
      · omega
    rw [or_iff_right hnb]
    exact hrail_iff qx rx y hrx
  have hbanRow_noBase : ∀ (qx rx : ℕ), qx < v → rx ≤ L → (0 < rx ∨ n ≤ qx) →
      banRow (qx * (L + 1) + rx) = emitNoBase w (qx * (L + 1) + rx) (L - rx) (v - 1 - qx) (L + 1) := by
    intro qx rx hqx hrx hor
    set x := qx * (L + 1) + rx
    have hk_eq : k = (x + 1) + ((L - rx) + (v - 1 - qx) * (L + 1)) := by
      have h1 : (v - 1 - qx + 1 + qx) = v := by omega
      have h2 : (v - 1 - qx + 1 + qx) * (L + 1) = v * (L + 1) := by rw [h1]
      have h3 : (v - 1 - qx + 1 + qx) * (L + 1) = qx * (L + 1) + (L + 1) + (v - 1 - qx) * (L + 1) := by ring
      show v * (L + 1) = _
      omega
    simp only [banRow]
    rw [hk_eq, list_range_add, List.filter_append]
    have hlow : (List.range (x + 1)).filter (fun y => decide (x < y ∧ ¬ good x y)) = [] := by
      apply filter_map_eq_nil
      intro y hy
      rw [List.mem_range] at hy
      simp only [decide_eq_false_iff_not]; omega
    rw [hlow, List.nil_append]
    by_cases hrxL : rx = L
    · have hsub0 : L - rx = 0 := by omega
      simp only [hsub0, Nat.zero_add, emitNoBase, ↓reduceIte, List.nil_append, Nat.add_zero]
      have hall : ((List.range ((v - 1 - qx) * (L + 1))).map (fun d => x + 1 + d)).filter
          (fun y => decide (x < y ∧ ¬ good x y)) =
          (List.range ((v - 1 - qx) * (L + 1))).map (fun d => x + 1 + d) := by
        apply filter_map_eq_all
        intro y hy
        rcases List.mem_map.mp hy with ⟨d, -, rfl⟩
        simp only [decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rw [hgood_noBase qx rx (x + 1 + d) (by omega) hor]
        omega
      rw [hall, List.flatMap_map]; rfl
    · have hsubpos : L - rx ≠ 0 := by omega
      have hsplit : (L - rx) + (v - 1 - qx) * (L + 1) = 1 + ((L - rx - 1) + (v - 1 - qx) * (L + 1)) := by omega
      rw [hsplit, list_range_add, List.map_append, List.filter_append]
      have h1 : ((List.range 1).map (fun d => x + 1 + d)).filter (fun y => decide (x < y ∧ ¬ good x y)) = [] := by
        simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.filter_cons, List.filter_nil]
        have hg : good x (x + 1) := (hgood_noBase qx rx (x + 1) (by omega) hor).mpr ⟨rfl, by omega⟩
        simp [hg]
      rw [h1, List.nil_append]
      have hall : (((List.range ((L - rx - 1) + (v - 1 - qx) * (L + 1))).map (fun d => 1 + d)).map
          (fun d => x + 1 + d)).filter (fun y => decide (x < y ∧ ¬ good x y)) =
          (List.range ((L - rx - 1) + (v - 1 - qx) * (L + 1))).map (fun d => x + 2 + d) := by
        rw [List.map_map]
        have hmap : (List.range ((L - rx - 1) + (v - 1 - qx) * (L + 1))).map ((fun d => x + 1 + d) ∘ (fun d => 1 + d)) =
            (List.range ((L - rx - 1) + (v - 1 - qx) * (L + 1))).map (fun d => x + 2 + d) := by
          apply List.map_congr_left; intro d _; dsimp only [Function.comp_apply]; omega
        rw [hmap]
        apply filter_map_eq_all
        intro y hy
        rcases List.mem_map.mp hy with ⟨d, -, rfl⟩
        simp only [decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rw [hgood_noBase qx rx (x + 2 + d) (by omega) hor]
        omega
      rw [hall, List.flatMap_map]
      simp only [emitNoBase, hsubpos, ↓reduceIte]
      rw [show x + 1 + (L - rx) = x + 2 + (L - rx - 1) by omega, ← emitRange_add]
      rfl
  have hbanRow_leftRx0 : ∀ (qx : ℕ) (hqx : qx < n),
      banRow (qx * (L + 1)) =
        emitLeftRx0 w (qx * (L + 1)) L (n - 1 - qx) ((List.finRange n).map (fun j => A ⟨qx, hqx⟩ j)) := by
    intro qx hqx
    set x := qx * (L + 1)
    have hgood0 : ∀ y : ℕ, good x y ↔
        (y = x + 1 ∨ ∃ j : Fin n, A ⟨qx, hqx⟩ j = true ∧ y = (n + j.val) * (L + 1)) := by
      intro y
      simp only [good]
      have hr := hrail_iff qx 0 y (by omega)
      simp only [Nat.add_zero] at hr
      rw [hr]
      have hLpos : 0 < L := by omega
      constructor
      · rintro (hb | ⟨h1, -⟩)
        · rcases (hbase_iff x y).mp hb with ⟨i, j, hA, hxi, hyj⟩
          have hiq : i = ⟨qx, hqx⟩ := Fin.ext (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos L) hxi.symm)
          subst hiq
          exact Or.inr ⟨j, hA, hyj⟩
        · exact Or.inl h1
      · rintro (rfl | ⟨j, hA, rfl⟩)
        · exact Or.inr ⟨rfl, hLpos⟩
        · exact Or.inl ((hbase_iff x _).mpr ⟨⟨qx, hqx⟩, j, hA, rfl, rfl⟩)

    have hk_eq : k = (x + 1) + (1 + (((L - 1) + (n - 1 - qx) * (L + 1)) + n * (L + 1))) := by
      have h1 : (n - 1 - qx + 1 + qx) * (L + 1) = n * (L + 1) := by rw [show n - 1 - qx + 1 + qx = n by omega]
      have h2 : (n - 1 - qx + 1 + qx) * (L + 1) = qx * (L + 1) + (L + 1) + (n - 1 - qx) * (L + 1) := by ring
      show 2 * n * (L + 1) = _
      have h3 : 2 * n * (L + 1) = n * (L + 1) + n * (L + 1) := by ring
      omega
    simp only [banRow]
    rw [hk_eq, list_range_add, List.filter_append]
    have hlow : (List.range (x + 1)).filter (fun y => decide (x < y ∧ ¬ good x y)) = [] := by
      apply filter_map_eq_nil; intro y hy; rw [List.mem_range] at hy; simp only [decide_eq_false_iff_not]; omega
    rw [hlow, List.nil_append, list_range_add, List.map_append, List.filter_append]
    have hrail1 : ((List.range 1).map (fun d => x + 1 + d)).filter (fun y => decide (x < y ∧ ¬ good x y)) = [] := by
      simp only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.filter_cons, List.filter_nil]
      have hg : good x (x + 1) := (hgood0 (x + 1)).mpr (Or.inl rfl)
      simp [hg]
    rw [hrail1, List.nil_append, list_range_add, List.map_append, List.map_append, List.filter_append,
        List.flatMap_append]

    have hmid_map : ((List.range ((L - 1) + (n - 1 - qx) * (L + 1))).map (fun d => 1 + d)).map
        (fun d => x + 1 + d) =
        (List.range ((L - 1) + (n - 1 - qx) * (L + 1))).map (fun d => x + 2 + d) := by
      rw [List.map_map]; apply List.map_congr_left; intro d _; dsimp only [Function.comp_apply]; omega
    have hmid_all : ((List.range ((L - 1) + (n - 1 - qx) * (L + 1))).map (fun d => x + 2 + d)).filter
        (fun y => decide (x < y ∧ ¬ good x y)) =
        (List.range ((L - 1) + (n - 1 - qx) * (L + 1))).map (fun d => x + 2 + d) := by
      apply filter_map_eq_all
      intro y hy
      rcases List.mem_map.mp hy with ⟨d, hd, rfl⟩
      rw [List.mem_range] at hd
      simp only [decide_eq_true_eq]
      refine ⟨by omega, ?_⟩
      rw [hgood0]
      rintro (h1 | ⟨j, -, h2⟩)
      · omega
      · have hlt : x + 2 + d < n * (L + 1) := by
          have h1 : (n - 1 - qx + 1 + qx) * (L + 1) = n * (L + 1) := by rw [show n - 1 - qx + 1 + qx = n by omega]
          have h2 : (n - 1 - qx + 1 + qx) * (L + 1) = qx * (L + 1) + (L + 1) + (n - 1 - qx) * (L + 1) := by ring
          omega
        have hge : n * (L + 1) ≤ (n + j.val) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
        omega

    have hbase_start : x + 1 + (1 + ((L - 1) + (n - 1 - qx) * (L + 1))) = n * (L + 1) := by
      have h1 : (n - 1 - qx + 1 + qx) * (L + 1) = n * (L + 1) := by rw [show n - 1 - qx + 1 + qx = n by omega]
      have h2 : (n - 1 - qx + 1 + qx) * (L + 1) = qx * (L + 1) + (L + 1) + (n - 1 - qx) * (L + 1) := by ring
      omega
    have hright_map : (((List.range (n * (L + 1))).map (fun d => (L - 1) + (n - 1 - qx) * (L + 1) + d)).map
        (fun d => 1 + d)).map (fun d => x + 1 + d) =
        (List.range (n * (L + 1))).map (fun d => n * (L + 1) + d) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left; intro d _; dsimp only [Function.comp_apply]; omega
    have hright_eq : (((List.range (n * (L + 1))).map (fun d => n * (L + 1) + d)).filter
        (fun y => decide (x < y ∧ ¬ good x y))).flatMap (fun y => emitPairBits w x y) =
        emitRow w x (n * (L + 1)) L ((List.finRange n).map (fun j => A ⟨qx, hqx⟩ j)) := by
      rw [list_range_mul_shift, List.filter_flatMap, list_flatMap_flatMap]
      have hfin : ∀ (m : ℕ) (hm : m ≤ n),
          ((List.range m).flatMap (fun q =>
            (((List.range (L + 1)).map (fun r => (n + (n - m) + q) * (L + 1) + r)).filter
              (fun y => decide (x < y ∧ ¬ good x y))).flatMap (fun y => emitPairBits w x y))) =
          emitRow w x ((n + (n - m)) * (L + 1)) L
            (((List.finRange n).drop (n - m)).map (fun j => A ⟨qx, hqx⟩ j)) := by
        intro m
        induction m with
        | zero => intro _; rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp), List.map_nil]; rfl
        | succ m ih =>
          intro hm
          have hj_lt : n - (m + 1) < n := by omega
          have hdrop_cons : (List.finRange n).drop (n - (m + 1)) =
              ⟨n - (m + 1), hj_lt⟩ :: (List.finRange n).drop (n - m) := by
            have h1 : n - (m + 1) < (List.finRange n).length := by simp; omega
            rw [List.drop_eq_getElem_cons h1]
            simp [show n - (m + 1) + 1 = n - m by omega]
          rw [List.range_succ_eq_map (n := m), List.flatMap_cons, List.flatMap_map, hdrop_cons,
              List.map_cons, emitRow]
          congr 1
          ·
            set j0 : Fin n := ⟨n - (m + 1), hj_lt⟩
            set y0 := (n + j0.val) * (L + 1)
            have hx_lt_y0 : x < y0 := by
              have : qx < n + j0.val := by omega
              exact Nat.mul_lt_mul_of_pos_right this (Nat.succ_pos L)
            have hblk_split : List.range (L + 1) = 0 :: (List.range L).map (fun r => r + 1) :=
              List.range_succ_eq_map
            have hmap0 : (List.range (L + 1)).map (fun r => (n + (n - (m + 1)) + 0) * (L + 1) + r) =
                y0 :: (List.range L).map ((fun r => y0 + r) ∘ (fun r => r + 1)) := by
              rw [hblk_split, List.map_cons, List.map_map]
              simp only [Nat.add_zero]
              rfl
            rw [hmap0, List.filter_cons]
            have h0good : good x y0 ↔ A ⟨qx, hqx⟩ j0 = true := by
              rw [hgood0]
              constructor
              · rintro (h1 | ⟨j, hA, h2⟩)
                · have hge : x + L + 1 ≤ y0 := by
                    have hqx1 : qx + 1 ≤ n + j0.val := by omega
                    have := Nat.mul_le_mul_right (L + 1) hqx1
                    have hexp : (qx + 1) * (L + 1) = x + L + 1 := by simp only [x]; ring
                    omega
                  omega
                · have hj : j = j0 := Fin.ext (by
                    have := Nat.eq_of_mul_eq_mul_right (Nat.succ_pos L) h2
                    omega)
                  subst hj; exact hA
              · intro hA; exact Or.inr ⟨j0, hA, rfl⟩
            have htail_all : ((List.range L).map ((fun r => y0 + r) ∘ (fun r => r + 1))).filter
                (fun y => decide (x < y ∧ ¬ good x y)) =
                (List.range L).map (fun r => y0 + 1 + r) := by
              have hcm : (List.range L).map ((fun r => y0 + r) ∘ (fun r => r + 1)) =
                  (List.range L).map (fun r => y0 + 1 + r) := by
                apply List.map_congr_left; intro r _; dsimp only [Function.comp_apply]; omega
              rw [hcm]
              apply filter_map_eq_all
              intro y hy
              rcases List.mem_map.mp hy with ⟨r, hr, rfl⟩
              rw [List.mem_range] at hr
              simp only [decide_eq_true_eq]
              refine ⟨by omega, ?_⟩
              rw [hgood0]
              rintro (h1 | ⟨j, -, h2⟩)
              · omega
              · have hmod1 : (y0 + 1 + r) % (L + 1) = r + 1 := by
                  rw [show y0 + 1 + r = (r + 1) + (L + 1) * (n + j0.val) by simp only [y0]; ring,
                      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
                have hmod2 : (y0 + 1 + r) % (L + 1) = 0 := by rw [h2, Nat.mul_mod_left]
                omega
            rw [htail_all]
            cases hA : A ⟨qx, hqx⟩ j0
            · have hng : ¬ good x y0 := by rw [h0good, hA]; decide
              simp only [Nat.add_zero, hx_lt_y0, hng, not_false_eq_true, and_self, decide_true,
                ↓reduceIte, List.flatMap_cons, List.flatMap_map, Bool.false_eq_true]
              rfl
            · have hg : good x y0 := h0good.mpr hA
              simp only [Nat.add_zero, hg, not_true_eq_false, and_false, decide_false,
                Bool.false_eq_true, ↓reduceIte, List.flatMap_map, List.nil_append]
              rfl
          · have hih := ih (by omega)
            have hshift : (n + (n - (m + 1))) * (L + 1) + (L + 1) = (n + (n - m)) * (L + 1) := by
              have : n + (n - (m + 1)) + 1 = n + (n - m) := by omega
              rw [← this]; ring
            rw [hshift, ← hih]
            apply List.flatMap_congr
            intro q _
            have hqeq : n + (n - (m + 1)) + (q + 1) = n + (n - m) + q := by omega
            simp only [Function.comp_apply, hqeq]
      have hfin0 := hfin n (le_refl n)
      simp only [Nat.sub_self, Nat.add_zero, List.drop_zero] at hfin0
      rw [← hfin0]
      apply List.flatMap_congr
      intro q _
      have hq : n * (L + 1) + q * (L + 1) = (n + q) * (L + 1) := by ring
      congr 1; congr 1
      apply List.map_congr_left; intro r _; omega
    rw [hmid_map, hmid_all, List.flatMap_map, hright_map, hright_eq]
    simp only [emitLeftRx0]
    have hstart1 : x + L + 1 = x + 2 + (L - 1) := by omega
    have hstart2 : x + L + 1 + (n - 1 - qx) * (L + 1) = n * (L + 1) := by omega
    rw [hstart2, hstart1, ← emitRange_add]; rfl

  have hnbLoop : ∀ (qx r : ℕ), qx < v → r ≤ L + 1 → (r ≤ L ∨ n ≤ qx) →
      emitNoBaseLoop w (qx * (L + 1) + (L + 1 - r)) (v - 1 - qx) (L + 1) r =
        (List.range r).flatMap (fun d => banRow (qx * (L + 1) + (L + 1 - r) + d)) := by
    intro qx r hqx hr hor
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [emitNoBaseLoop, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      have h0 := hbanRow_noBase qx (L + 1 - (r + 1)) hqx (by omega) (by omega)
      have hsub : L - (L + 1 - (r + 1)) = r := by omega
      rw [hsub] at h0
      rw [Nat.add_zero, ← h0]
      congr 1
      have hih := ih (by omega) (Or.inl (by omega))
      have hstep : qx * (L + 1) + (L + 1 - (r + 1)) + 1 = qx * (L + 1) + (L + 1 - r) := by omega
      rw [hstep, hih]
      apply List.flatMap_congr
      intro d _
      show banRow (qx * (L + 1) + (L + 1 - r) + d) = banRow (qx * (L + 1) + (L + 1 - (r + 1)) + (d + 1))
      congr 1; omega

  have hleft_eq : ∀ (m : ℕ), m ≤ n →
      emitLeftBlocks w L n m ((n - m) * (L + 1)) (v - (n - m)) (a.drop ((n - m) * n)) =
        (List.range (m * (L + 1))).flatMap (fun d => banRow ((n - m) * (L + 1) + d)) := by
    intro m
    induction m with
    | zero => intro _; simp [emitLeftBlocks]
    | succ m ih =>
      intro hm
      have hqx : n - (m + 1) < n := by omega
      set qx := n - (m + 1)
      simp only [emitLeftBlocks]

      have hrow_eq : (List.range n).map (fun i => (a.drop (qx * n)).getD i false) =
          (List.finRange n).map (fun j => A ⟨qx, hqx⟩ j) := by
        rw [cells_map_drop n A qx (by omega)]
        have hdrop_cons : (List.finRange n).drop qx = ⟨qx, hqx⟩ :: (List.finRange n).drop (qx + 1) := by
          have h1 : qx < (List.finRange n).length := by simp; omega
          rw [List.drop_eq_getElem_cons h1]; simp
        rw [hdrop_cons, List.flatMap_cons]
        have hrow_len : ((List.finRange n).map (fun j => A ⟨qx, hqx⟩ j)).length = n := by simp
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
          have hi : i < n := by simp at hi1; exact hi1
          have hi' : i < ((List.finRange n).map (fun j => A ⟨qx, hqx⟩ j) ++
              ((List.finRange n).drop (qx + 1)).flatMap (fun i => (List.finRange n).map (fun j => A i j))).length := by
            simp; omega
          rw [List.getD_eq_getElem _ _ hi', List.getElem_append_left (by simp; omega)]
          simp
      have hrx0 := hbanRow_leftRx0 qx hqx
      have hm_eq : n - 1 - qx = m := by omega
      rw [hm_eq] at hrx0
      have hrem_eq : v - qx - 1 = v - 1 - qx := by omega
      have hnb := hnbLoop qx L (by omega) (by omega) (Or.inl le_rfl)
      have hLsub : L + 1 - L = 1 := by omega
      rw [hLsub] at hnb
      have hih := ih (by omega)
      have hqx1 : n - m = qx + 1 := by omega
      have hdrop2 : (a.drop (qx * n)).drop n = a.drop ((n - m) * n) := by
        rw [List.drop_drop, hqx1, Nat.succ_mul, Nat.add_comm]
      have hx_next : qx * (L + 1) + L + 1 = (n - m) * (L + 1) := by rw [hqx1]; ring
      have hra_next : v - 1 - qx = v - (n - m) := by omega
      rw [hrow_eq, ← hrx0, hrem_eq, hnb, hdrop2, hx_next, hra_next, hih]

      rw [Nat.succ_mul, Nat.add_comm (m * (L + 1)), list_range_add, List.flatMap_append]
      congr 1
      · rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, Nat.add_zero]
        congr 1
        apply List.flatMap_congr; intro d _
        show banRow (qx * (L + 1) + 1 + d) = banRow (qx * (L + 1) + (d + 1))
        congr 1; omega
      · rw [List.flatMap_map]
        apply List.flatMap_congr; intro d _
        show banRow ((n - m) * (L + 1) + d) = banRow (qx * (L + 1) + (L + 1 + d))
        congr 1; rw [hqx1]; ring

  have hright_eq : ∀ (m : ℕ), m ≤ n →
      emitRightBlocks w L m ((v - m) * (L + 1)) m =
        (List.range (m * (L + 1))).flatMap (fun d => banRow ((v - m) * (L + 1) + d)) := by
    intro m
    induction m with
    | zero => intro _; simp [emitRightBlocks]
    | succ m ih =>
      intro hm
      set qx := v - (m + 1)
      simp only [emitRightBlocks]
      have hnb := hnbLoop qx (L + 1) (by omega) le_rfl (Or.inr (by omega))
      have hsub0 : L + 1 - (L + 1) = 0 := Nat.sub_self _
      have hra : v - 1 - qx = m := by omega
      rw [hsub0, Nat.add_zero, hra] at hnb
      have hih := ih (by omega)
      have hqx1 : v - m = qx + 1 := by omega
      have hx_next : qx * (L + 1) + L + 1 = (v - m) * (L + 1) := by rw [hqx1]; ring
      rw [show m + 1 - 1 = m by omega, hnb, hx_next, hih]
      rw [show (m + 1) * (L + 1) = (L + 1) + m * (L + 1) by ring,
          list_range_add (L + 1) (m * (L + 1)), List.flatMap_append]
      congr 1
      rw [List.flatMap_map]
      apply List.flatMap_congr; intro d _
      show banRow ((v - m) * (L + 1) + d) = banRow (qx * (L + 1) + (L + 1 + d))
      congr 1; rw [hqx1]; ring
  have hLfull := hleft_eq n (le_refl n)
  have hRfull := hright_eq n (le_refl n)
  simp only [Nat.sub_self, Nat.zero_mul, Nat.sub_zero, List.drop_zero, Nat.zero_add] at hLfull
  have hvn : v - n = n := by omega
  rw [hvn] at hRfull
  rw [hLfull, hRfull]
  have hk_split : k = n * (L + 1) + n * (L + 1) := by show 2 * n * (L + 1) = _; ring
  rw [hk_split, list_range_add (n * (L + 1)) (n * (L + 1)), List.flatMap_append, List.flatMap_map]

end PEqualNP.Outside.L_meta_32063.WriteM


theorem PEqualNP.Outside.L_meta_32063 :
  let header := fun n : Nat => List.replicate n true ++ [false]
  let field := fun (k z : Nat) => (List.range (k.log2+1)).map (fun h => z.testBit h)
  let fast := fun f : List Bool → List Bool =>
    ∃ M : Turing.TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f,
      ∀ i, Finite (M.tm.Γ i)
  ∃ write read : List Bool → List Bool, fast write ∧ fast read ∧
    ∀ (n : Nat), 0 < n → ∀ A : Fin n → Fin n → Bool,
      let v := 2*n
      let L := 2*(1+v*((v+1).log2+1))
      let k := v*(L+1)
      let b := Nat.fib (L+2)
      let B : Matrix (Fin n) (Fin n) Nat := fun i j => (A i j).toNat
      let cells := (List.finRange n).flatMap (fun i => (List.finRange n).map (fun j => (i,j)))
      let base := (cells.filter (fun z => A z.1 z.2)).map (fun z =>
        (z.1.val*(L+1),(n+z.2.val)*(L+1)))
      let good := fun (x y : Nat) => (x,y) ∈ base ∨ (y = x+1 ∧ x/(L+1) = y/(L+1))
      let ban := (List.range k).flatMap (fun x => ((List.range k).filter (fun y =>
        decide (x < y ∧ ¬ good x y))).map (fun y => (x,y)))
      let Fn := (Fin k → Bool) → (Fin k → Bool) → Bool
      let fits := fun f : Fn => (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size+1 ≤ 2*k ∧
        PEqualNP.Represents.Represents (fun i j : Fin k => decide (i=j)) C ∧
        ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
        ∀ e ∈ ban, f (fun i => decide (i.val = e.1 ∨ i.val = e.2)) (fun _ => false) = false
      let Z := Nat.card {f : Fn // fits f}
      write (header n ++ cells.map (fun z => A z.1 z.2)) =
        header k ++ ban.flatMap (fun e => field k e.1 ++ field k e.2) ∧
      fits (fun x y => decide (∃ i, x i = true ∧ y i = true)) ∧
      v.factorial < b ∧ Z % b = B.permanent ∧
      read (header n ++ Z.bits) = B.permanent.bits := by
  refine ⟨PEqualNP.Outside.L_meta_32063.WriteM.writeFn,
    PEqualNP.Outside.L_meta_32063.ReadM.readFn,
    PEqualNP.Outside.L_meta_32063.WriteM.write_fast,
    PEqualNP.Outside.L_meta_32063.ReadM.read_fast, ?_⟩
  intro n hn A
  have hmod := PEqualNP.Outside.L_meta_32063.Bridge.Z_mod_b_eq_permanent n hn A
  refine ⟨PEqualNP.Outside.L_meta_32063.WriteM.writeFn_on_valid n hn A,
    PEqualNP.Outside.L_meta_32063.Bridge.fits_identity n hn _,
    PEqualNP.Outside.L_meta_32063.Bridge.fact_lt_fib_L n,
    hmod, ?_⟩
  rw [PEqualNP.Outside.L_meta_32063.ReadM.readFn_on_valid n, hmod]
