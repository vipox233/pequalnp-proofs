import PEqualNP.Defs
import Mathlib.Tactic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases



namespace PEqualNP.Outside.L_lib_853.R012.TightReadOnce

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



/-- Read-once positive AND/OR formulas, indexed by their exact leaf set. -/
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

/-- Equality in the fan-in-two input bound forces a positive read-once formula. -/
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

end PEqualNP.Outside.L_lib_853.R012.TightReadOnce


namespace PEqualNP.Outside.L_lib_853.R012.ReadOncePath
open PEqualNP.Outside.L_lib_853.R012.TightReadOnce

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

end PEqualNP.Outside.L_lib_853.R012.ReadOncePath


namespace PEqualNP.Outside.L_lib_853.R017

open PEqualNP.Outside.L_lib_853.R012.TightReadOnce PEqualNP.Outside.L_lib_853.R012.ReadOncePath

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

end PEqualNP.Outside.L_lib_853.R017


namespace PEqualNP.Outside.L_lib_853.R017

open PEqualNP.Outside.L_lib_853.R012.TightReadOnce PEqualNP.Outside.L_lib_853.R012.ReadOncePath

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

end PEqualNP.Outside.L_lib_853.R017


namespace PEqualNP.Outside.L_lib_853.R017
open PEqualNP.Outside.L_lib_853.R012.TightReadOnce PEqualNP.Outside.L_lib_853.R012.ReadOncePath
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

end PEqualNP.Outside.L_lib_853.R017


namespace PEqualNP.Outside.L_lib_853.R017

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

end PEqualNP.Outside.L_lib_853.R017


namespace PEqualNP.Outside.L_lib_853.R017
open PEqualNP.Outside.L_lib_853.R012.TightReadOnce PEqualNP.Outside.L_lib_853.R012.ReadOncePath
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

end PEqualNP.Outside.L_lib_853.R017


namespace PEqualNP.Outside.L_lib_853.R017.RowColumn
open PEqualNP.Outside.L_lib_853.R012.TightReadOnce PEqualNP.Outside.L_lib_853.R012.ReadOncePath
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
    (hf : RO Finset.univ f) (hm : PEqualNP.Outside.L_lib_853.R017.Matched mate color Finset.univ f) :
    ∃ p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, f (Fin.append x y) = invFunction p x y := by
  classical
  obtain ⟨p, hpi, hcol, hcomm, hout, hfn, hedge⟩ :=
    PEqualNP.Outside.L_lib_853.R017.matched_involution_normal_form mate_involutive color_mate hf hm
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
    (hf : RO Finset.univ f) (hm : PEqualNP.Outside.L_lib_853.R017.Matched mate color Finset.univ f) :
    ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
      ∀ x y, f (Fin.append x y) = invFunction p x y := by
  obtain ⟨p, hp, he⟩ := ro_equality_normal_form f hf hm
  refine ⟨p, ⟨hp, he⟩, ?_⟩
  intro q hq
  apply invFunction_injective q p hq.1 hp
  intro x y
  exact (hq.2 x y).symm.trans (he x y)

end PEqualNP.Outside.L_lib_853.R017.RowColumn


namespace PEqualNP.Outside.L_lib_853.R017.RowColumn
open PEqualNP.Outside.L_lib_853.R012.TightReadOnce PEqualNP.Outside.L_lib_853.R012.ReadOncePath
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
    PEqualNP.Outside.L_lib_853.R017.Matched mate color Finset.univ f := by
  have hs : PEqualNP.Outside.L_lib_853.R017.NoSingle f := by
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

end PEqualNP.Outside.L_lib_853.R017.RowColumn


namespace PEqualNP.Outside.L_lib_853.R017.CircuitForward

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_lib_853.R012.TightReadOnce PEqualNP.Outside.L_lib_853.R012.ReadOncePath
open PEqualNP.Outside.L_lib_853.R017.RowColumn

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

end PEqualNP.Outside.L_lib_853.R017.CircuitForward


namespace PEqualNP.Outside.L_lib_853.R017

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

end PEqualNP.Outside.L_lib_853.R017


namespace PEqualNP.Outside.L_lib_853.R020.ROCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_lib_853.R012.TightReadOnce

variable {n : ℕ}

def GateOK (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

/-- Compilation after an arbitrary initial list. The first n wires retain the input variables. -/
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

/-- A positive read-once formula compiles to exactly one fewer gate than leaves. -/
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

end PEqualNP.Outside.L_lib_853.R020.ROCompiler


namespace PEqualNP.Outside.L_lib_853.R019.InvolutionRO

open PEqualNP.Outside.L_lib_853.R012.TightReadOnce PEqualNP.Outside.L_lib_853.R012.ReadOncePath PEqualNP.Outside.L_lib_853.R017.RowColumn

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

end PEqualNP.Outside.L_lib_853.R019.InvolutionRO


namespace PEqualNP.Outside.L_lib_853.R019.InverseBridge
open PEqualNP.Outside.L_lib_853.R017.RowColumn PEqualNP.Outside.L_lib_853.R012.TightReadOnce PEqualNP.Outside.L_lib_853.R012.ReadOncePath
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

end PEqualNP.Outside.L_lib_853.R019.InverseBridge


namespace PEqualNP.Outside.L_lib_853.R019

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
  · exact PEqualNP.Outside.L_lib_853.R017.official_forward k hk f
  · rintro ⟨p, ⟨hp, hf⟩, hu⟩
    obtain ⟨C, hm, hs, hr, he⟩ := InverseBridge.involution_circuit_of_compiler
      (fun h => PEqualNP.Outside.L_lib_853.R020.ROCompiler.ro_circuit_exists h) (by omega : 0 < k) p hp
    refine ⟨C, hm, hs, hr, ?_⟩
    intro x y
    exact (hf x y).trans (he x y).symm

end PEqualNP.Outside.L_lib_853.R019

theorem PEqualNP.Outside.L_lib_853 :
∀ (k : Nat), 2 ≤ k → ∀ f : (Fin k → Bool) → (Fin k → Bool) → Bool,
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size + 1 ≤ 2*k ∧
    PEqualNP.Represents.Represents (fun i j : Fin k => decide (i = j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ↔
  ∃! p : Equiv.Perm (Fin k), Function.Involutive p ∧
    ∀ x y, f x y = decide (∃ i : Fin k,
        (x i = true ∧ y i = true) ∨
        (p i ≠ i ∧ ((x i = true ∧ x (p i) = true) ∨
          (y i = true ∧ y (p i) = true)))) := PEqualNP.Outside.L_lib_853.R019.official_full
