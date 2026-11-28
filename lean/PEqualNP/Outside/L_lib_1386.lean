import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1386
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wr (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wr_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wr (g :: gs) x = wr gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

theorem wr_app (a b : List Gate) (x : List Bool) : wr (a ++ b) x = wr b (wr a x) := by
  simp [wr, List.foldl_append]

theorem wr_len (gs : List Gate) : ∀ x : List Bool, (wr gs x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; rfl
  | cons g gs ih =>
    intro x
    rw [wr_cons, ih, List.length_append, List.length_singleton, List.length_cons]; omega

theorem gd_oob (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false
      = if i < w.length then w.getD i false else if i = w.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    rw [hk]; rfl

theorem wr_input (gs : List Gate) : ∀ (x : List Bool) (i : ℕ), i < x.length →
    (wr gs x).getD i false = x.getD i false := by
  induction gs with
  | nil => intro x i _; rfl
  | cons g gs ih =>
    intro x i hi
    rw [wr_cons, ih _ i (by rw [List.length_append, List.length_singleton]; omega), getD_snoc,
      if_pos hi]

theorem monoZ (zi : ℕ) : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ g ∈ gs, zi ∉ g.inputs) → ∀ w1 w2 : List Bool, w1.length = w2.length →
    (∀ i, i ≠ zi → w1.getD i false = true → w2.getD i false = true) →
    ∀ i, i ≠ zi → (wr gs w1).getD i false = true → (wr gs w2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ _ w1 w2 _ h; exact h
  | cons g gs ih =>
    intro hm hz w1 w2 hl h
    rw [wr_cons, wr_cons]
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hz g' (List.mem_cons_of_mem _ hg'))
    · rw [List.length_append, List.length_append, hl, List.length_singleton, List.length_singleton]
    intro i hi
    rw [getD_snoc, getD_snoc, hl]
    split_ifs with a b
    · exact h i hi
    · have hop := (hm g (by simp)).1
      have hzg := hz g (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hop | hop
      · rw [hop]
        intro hh
        have hh' : ((g.inputs.map fun i => w1.getD i false).all id) = true := hh
        show ((g.inputs.map fun i => w2.getD i false).all id) = true
        rw [List.all_eq_true] at hh' ⊢
        intro b hb
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        exact h y (fun e => hzg (e ▸ hy)) (hh' _ (List.mem_map.mpr ⟨y, hy, rfl⟩))
      · rw [hop]
        intro hh
        have hh' : ((g.inputs.map fun i => w1.getD i false).any id) = true := hh
        show ((g.inputs.map fun i => w2.getD i false).any id) = true
        rw [List.any_eq_true] at hh' ⊢
        obtain ⟨b, hb, hbt⟩ := hh'
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        exact ⟨_, List.mem_map.mpr ⟨y, hy, rfl⟩, h y (fun e => hzg (e ▸ hy)) hbt⟩
    · exact id

theorem onelen {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneval {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  unfold oneEach
  by_cases hi : i < n
  · rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact hi)]
    have e : decide (i = u.val ∨ i = n + v.val) = decide (i = u.val) :=
      decide_eq_decide.mpr (by omega)
    rw [e]
    simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff]
  · rw [List.getD_append_right _ _ _ _ (by rw [List.length_ofFn]; omega), List.length_ofFn]
    by_cases h2 : i - n < m
    · have e : decide (i = u.val ∨ i = n + v.val) = decide (i - n = v.val) :=
        decide_eq_decide.mpr (by omega)
      rw [e]
      simp [List.getD_eq_getElem?_getD, h2, Fin.ext_iff]
    · have e : ¬ (i = u.val ∨ i = n + v.val) := by omega
      rw [decide_eq_false e, gd_oob _ _ (by rw [List.length_ofFn]; omega)]

/-! Forward direction: one OR gate joins the old and the new column. -/

def gO (i j : ℕ) : Gate := ⟨GateOp.or, [i, j]⟩
def rl (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩
def rho (n m c i : ℕ) : ℕ := if i = n + c then n + m + 2 else if i < n + m + 1 then i else i + 2

def FInv (ρ : ℕ → ℕ) (L : ℕ) (w w' : List Bool) : Prop :=
  L ≤ w.length ∧ w'.length = w.length + 2 ∧ ∀ i, w'.getD (ρ i) false = w.getD i false

theorem fsim (ρ : ℕ → ℕ) (L : ℕ) (h1 : ∀ i, i < L → ρ i < L + 2) (h2 : ∀ i, L ≤ i → ρ i = i + 2) :
    ∀ (gs : List Gate) (w w' : List Bool), FInv ρ L w w' →
      FInv ρ L (wr gs w) (wr (gs.map (rl ρ)) w') := by
  intro gs
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    intro w w' hI
    obtain ⟨a, b, c⟩ := hI
    have hv : GateOp.eval g.op ((g.inputs.map ρ).map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      rw [List.map_map]; congr 1; apply List.map_congr_left; intro y _; exact c y
    show FInv ρ L (wr gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]))
      (wr (gs.map (rl ρ)) (w' ++ [GateOp.eval g.op ((g.inputs.map ρ).map fun i => w'.getD i false)]))
    rw [hv]
    apply ih
    refine ⟨by rw [List.length_append, List.length_singleton]; omega,
      by rw [List.length_append, List.length_append, List.length_singleton, b], ?_⟩
    intro i
    rw [getD_snoc w', getD_snoc w, b]
    have hρ : (ρ i < w.length + 2 ↔ i < w.length) ∧ (ρ i = w.length + 2 ↔ i = w.length) := by
      by_cases hi : i < L
      · have := h1 i hi; constructor <;> omega
      · have := h2 i (by omega); constructor <;> omega
    simp only [hρ.1, hρ.2]
    split_ifs
    · exact c i
    · rfl
    · rfl

theorem fwd (n m : ℕ) (A : Fin n → Fin (m+1) → Bool) (c : Fin (m+1)) (k : ℕ)
    (hA : RepSizeAtMost A k) :
    RepSizeAtMost (fun (u : Fin n) (j : Fin (m+2)) =>
      if h : j.val < m+1 then A u ⟨j.val,h⟩ else A u c) (k+1) := by
  obtain ⟨C, hmono, hsize, hrep⟩ := hA
  have hc := c.isLt
  refine ⟨⟨gO (n + c.val) (n + m + 1) :: C.gates.map (rl (rho n m c.val)), rho n m c.val C.output⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by simp [gO], by simp [gO]⟩
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have := hmono g' hg'
      exact ⟨this.1, by simp only [rl, List.length_map]; exact this.2⟩
  · show (gO (n + c.val) (n + m + 1) :: C.gates.map (rl (rho n m c.val))).length ≤ k + 1
    rw [List.length_cons, List.length_map]
    have : C.gates.length ≤ k := hsize
    omega
  · intro u j
    have hu := u.isLt
    have hj := j.isLt
    obtain ⟨v', hv'⟩ : ∃ v' : Fin (m+1), (v'.val = j.val ∧ j.val < m+1 ∨ v'.val = c.val ∧ j.val = m+1) ∧
        (if h : j.val < m+1 then A u ⟨j.val,h⟩ else A u c) = A u v' := by
      by_cases h : j.val < m+1
      · exact ⟨⟨j.val, h⟩, Or.inl ⟨rfl, h⟩, dif_pos h⟩
      · exact ⟨c, Or.inr ⟨rfl, by omega⟩, dif_neg h⟩
    show (wr (gO (n + c.val) (n + m + 1) :: C.gates.map (rl (rho n m c.val))) (oneEach u j)).getD
      (rho n m c.val C.output) false = (if h : j.val < m+1 then A u ⟨j.val,h⟩ else A u c)
    rw [hv'.2, ← hrep u v', wr_cons]
    have F0 : FInv (rho n m c.val) (n + m + 1) (oneEach u v')
        (oneEach u j ++ [(gO (n + c.val) (n + m + 1)).op.eval
          ((gO (n + c.val) (n + m + 1)).inputs.map fun i => (oneEach u j).getD i false)]) := by
      refine ⟨by rw [onelen]; omega,
        by rw [List.length_append, onelen, onelen, List.length_singleton]; omega, ?_⟩
      intro i
      have horv : (gO (n + c.val) (n + m + 1)).op.eval
          ((gO (n + c.val) (n + m + 1)).inputs.map fun i => (oneEach u j).getD i false)
          = (decide (n + c.val = u.val ∨ n + c.val = n + j.val)
              || decide (n + m + 1 = u.val ∨ n + m + 1 = n + j.val)) := by
        show ((oneEach u j).getD (n + c.val) false || ((oneEach u j).getD (n + m + 1) false || false)) = _
        rw [oneval, oneval, Bool.or_false]
      rw [horv, getD_snoc, onelen, oneval, oneval]
      have hv1 := hv'.1
      by_cases hi1 : i = n + c.val
      · have hr : rho n m c.val i = n + m + 2 := by unfold rho; rw [if_pos hi1]
        rw [hr, if_neg (by omega), if_pos (by omega)]
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        omega
      · by_cases hi2 : i < n + m + 1
        · have hr : rho n m c.val i = i := by unfold rho; rw [if_neg hi1, if_pos hi2]
          rw [hr, if_pos (by omega)]
          exact decide_eq_decide.mpr (by omega)
        · have hr : rho n m c.val i = i + 2 := by unfold rho; rw [if_neg hi1, if_neg hi2]
          rw [hr, if_neg (by omega), if_neg (by omega)]
          exact (decide_eq_false (by omega)).symm
    exact (fsim (rho n m c.val) (n + m + 1)
      (by intro i hi; unfold rho; split_ifs <;> omega)
      (by intro i hi; unfold rho; split_ifs <;> omega) C.gates _ _ F0).2.2 C.output

/-! Reverse direction: set the new input to false and delete one gate that reads it. -/

def sg (D : ℕ → ℕ) (zi M T i : ℕ) : ℕ := if i < T ∧ i ≠ zi then D i else M

def mapT (D : ℕ → ℕ) (zi M : ℕ) : List Gate → ℕ → List Gate
  | [], _ => []
  | g :: gs, T => ⟨g.op, g.inputs.map (sg D zi M T)⟩ :: mapT D zi M gs (T + 1)

theorem mapT_len (D : ℕ → ℕ) (zi M : ℕ) (gs : List Gate) :
    ∀ T, (mapT D zi M gs T).length = gs.length := by
  induction gs with
  | nil => intro T; rfl
  | cons g gs ih => intro T; show (mapT D zi M gs (T + 1)).length + 1 = gs.length + 1; rw [ih]

theorem mapT_mono (D : ℕ → ℕ) (zi M : ℕ) (gs : List Gate) :
    ∀ T, (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ g ∈ mapT D zi M gs T, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs with
  | nil => intro T _ g hg; exact absurd hg (by simp [mapT])
  | cons g gs ih =>
    intro T h g' hg'
    have hg'' : g' = ⟨g.op, g.inputs.map (sg D zi M T)⟩ ∨ g' ∈ mapT D zi M gs (T + 1) :=
      List.mem_cons.mp hg'
    rcases hg'' with rfl | hg''
    · have := h g (by simp)
      exact ⟨this.1, by simp only [List.length_map]; exact this.2⟩
    · exact ih _ (fun g hg => h g (List.mem_cons_of_mem _ hg)) g' hg''

def Inv (D : ℕ → ℕ) (zi c M L0 : ℕ) (w w' : List Bool) : Prop :=
  L0 ≤ w.length ∧ w.length = w'.length + c ∧ w.getD zi false = false ∧
    ∀ i, i < w.length → i ≠ zi →
      (D i < w'.length ∨ M ≤ D i) ∧ w'.getD (D i) false = w.getD i false

theorem Inv_sg {D : ℕ → ℕ} {zi c M L0 : ℕ} {w w' : List Bool} (hI : Inv D zi c M L0 w w')
    (hM : w'.length ≤ M) (y : ℕ) :
    (sg D zi M w.length y < w'.length ∨ M ≤ sg D zi M w.length y) ∧
      w'.getD (sg D zi M w.length y) false = w.getD y false := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  unfold sg
  by_cases h : y < w.length ∧ y ≠ zi
  · rw [if_pos h]; exact h4 y h.1 h.2
  · rw [if_neg h]
    refine ⟨Or.inr le_rfl, ?_⟩
    rw [gd_oob _ _ hM]
    by_cases hy : y = zi
    · rw [hy, h3]
    · rw [gd_oob _ _ (by omega)]

theorem sim (D : ℕ → ℕ) (zi c M L0 : ℕ) (hD : ∀ i, L0 ≤ i → D i = i - c) (hz : zi < L0) :
    ∀ (gs : List Gate) (w w' : List Bool), Inv D zi c M L0 w w' → w'.length + gs.length ≤ M →
      Inv D zi c M L0 (wr gs w) (wr (mapT D zi M gs w.length) w') := by
  intro gs
  induction gs with
  | nil => intro w w' hI _; exact hI
  | cons g gs ih =>
    intro w w' hI hM
    rw [List.length_cons] at hM
    have hsg := Inv_sg hI (by omega)
    obtain ⟨h1, h2, h3, h4⟩ := hI
    have hv : GateOp.eval g.op ((g.inputs.map (sg D zi M w.length)).map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      rw [List.map_map]; congr 1; apply List.map_congr_left; intro y _; exact (hsg y).2
    show Inv D zi c M L0 (wr gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]))
      (wr (mapT D zi M gs (w.length + 1))
        (w' ++ [GateOp.eval g.op ((g.inputs.map (sg D zi M w.length)).map fun i => w'.getD i false)]))
    rw [hv]
    obtain ⟨v, hvd⟩ : ∃ v, v = g.op.eval (g.inputs.map fun i => w.getD i false) := ⟨_, rfl⟩
    rw [← hvd]
    have hI' : Inv D zi c M L0 (w ++ [v]) (w' ++ [v]) := by
      refine ⟨by rw [List.length_append, List.length_singleton]; omega,
        by rw [List.length_append, List.length_append, List.length_singleton]; omega,
        by rw [getD_snoc, if_pos (by omega)]; exact h3, ?_⟩
      intro i hi hne
      rw [List.length_append, List.length_singleton] at hi
      rw [List.length_append, List.length_singleton]
      by_cases hiw : i < w.length
      · obtain ⟨hb, hval⟩ := h4 i hiw hne
        rw [getD_snoc w v, if_pos hiw]
        rcases hb with hb | hb
        · exact ⟨Or.inl (by omega), by rw [getD_snoc w' v, if_pos hb]; exact hval⟩
        · refine ⟨Or.inr hb, ?_⟩
          rw [getD_snoc w' v, if_neg (by omega), if_neg (by omega), ← hval, gd_oob _ _ (by omega)]
      · have hiw' : i = w.length := by omega
        have hd : D i = w'.length := by rw [hD i (by omega)]; omega
        rw [hd, getD_snoc w' v, if_neg (lt_irrefl _), if_pos rfl, getD_snoc w v, if_neg hiw,
          if_pos hiw']
        exact ⟨Or.inl (by omega), rfl⟩
    have key := ih (w ++ [v]) (w' ++ [v]) hI'
      (by rw [List.length_append, List.length_singleton]; omega)
    rw [List.length_append, List.length_singleton] at key
    exact key

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

def sub (D : ℕ → ℕ) (zi M T : ℕ) (g : Gate) : ℕ :=
  if isOr g.op = true then
    (match g.inputs with
      | [a, b] => if a = zi then sg D zi M T b else sg D zi M T a
      | _ => M)
  else M

theorem sub_val (D : ℕ → ℕ) (zi c M L0 : ℕ) (w w' : List Bool) (hI : Inv D zi c M L0 w w')
    (hM : w'.length ≤ M) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hz : zi ∈ g.inputs) :
    (sub D zi M w.length g < w'.length ∨ M ≤ sub D zi M w.length g) ∧
      w'.getD (sub D zi M w.length g) false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, inputs⟩ := g
  have hz0 := hI.2.2.1
  have hMiss : w'.getD M false = false := gd_oob _ _ hM
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · have hs : sub D zi M w.length ⟨GateOp.and, inputs⟩ = M := rfl
    rw [hs]
    refine ⟨Or.inr le_rfl, ?_⟩
    rw [hMiss]; symm
    show (inputs.map fun i => w.getD i false).all id = false
    rw [List.all_eq_false]
    refine ⟨_, List.mem_map.mpr ⟨zi, hz, rfl⟩, ?_⟩
    show ¬ (w.getD zi false = true)
    rw [hz0]; exact Bool.false_ne_true
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · exact absurd hz (by simp)
    · have ha : a = zi := (List.mem_singleton.mp hz).symm
      have hs : sub D zi M w.length ⟨GateOp.or, [a]⟩ = M := rfl
      rw [hs]
      refine ⟨Or.inr le_rfl, ?_⟩
      rw [hMiss]
      show false = (w.getD a false || false)
      rw [ha, hz0]; rfl
    · by_cases ha : a = zi
      · have hs : sub D zi M w.length ⟨GateOp.or, [a, b]⟩ = sg D zi M w.length b := by
          show (if a = zi then sg D zi M w.length b else sg D zi M w.length a) = _
          rw [if_pos ha]
        rw [hs]
        have h := Inv_sg hI hM b
        refine ⟨h.1, ?_⟩
        rw [h.2]
        show _ = (w.getD a false || (w.getD b false || false))
        rw [ha, hz0, Bool.or_false, Bool.false_or]
      · have hb : b = zi := by
          rcases List.mem_cons.mp hz with h | h
          · exact absurd h.symm ha
          · exact (List.mem_singleton.mp h).symm
        have hs : sub D zi M w.length ⟨GateOp.or, [a, b]⟩ = sg D zi M w.length a := by
          show (if a = zi then sg D zi M w.length b else sg D zi M w.length a) = _
          rw [if_neg ha]
        rw [hs]
        have h := Inv_sg hI hM a
        refine ⟨h.1, ?_⟩
        rw [h.2]
        show _ = (w.getD a false || (w.getD b false || false))
        rw [hb, hz0, Bool.or_false, Bool.or_false]
    · exact absurd hl (by simp)

def D1 (zi i : ℕ) : ℕ := if i < zi then i else i - 1
def D2 (zi t s i : ℕ) : ℕ := if i < t then D1 zi i else if i = t then s else i - 2

theorem rev (n m : ℕ) (A : Fin n → Fin (m+1) → Bool) (c : Fin (m+1))
    (hw : ∃ (u : Fin n) (v : Fin (m+1)), A u c = true ∧ A u v = false) (k : ℕ)
    (hB : RepSizeAtMost (fun (u : Fin n) (j : Fin (m+2)) =>
      if h : j.val < m+1 then A u ⟨j.val,h⟩ else A u c) (k+1)) :
    RepSizeAtMost A k := by
  obtain ⟨C, hmono, hsize, hrep⟩ := hB
  have hsize' : C.gates.length ≤ k + 1 := hsize
  by_cases hread : ∃ g ∈ C.gates, (n+m+1) ∈ g.inputs
  · obtain ⟨g, hg, hzg⟩ := hread
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    have hlenG : C.gates.length = pre.length + post.length + 1 := by
      rw [hsplit, List.length_append, List.length_cons]; omega
    have hgm := hmono g hg
    have hpre : ∀ g' ∈ pre, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' h' => hmono g' (by rw [hsplit]; exact List.mem_append_left _ h')
    have hpost : ∀ g' ∈ post, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' h' => hmono g' (by rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h'))
    obtain ⟨zi, hzi⟩ : ∃ zi, zi = n+m+1 := ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ M, M = n+m+2+C.gates.length := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t = n+m+2+pre.length := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s, s = sub (D1 zi) zi M t g := ⟨_, rfl⟩
    rw [← hzi] at hzg
    refine ⟨⟨mapT (D1 zi) zi M pre (n+m+2) ++ mapT (D2 zi t s) zi M post (t+1),
      sg (D2 zi t s) zi M (t+1+post.length) C.output⟩, ?_, ?_, ?_⟩
    · intro g' hg'
      rcases List.mem_append.mp hg' with h | h
      · exact mapT_mono _ _ _ _ _ hpre g' h
      · exact mapT_mono _ _ _ _ _ hpost g' h
    · show (mapT (D1 zi) zi M pre (n+m+2) ++ mapT (D2 zi t s) zi M post (t+1)).length ≤ k
      rw [List.length_append, mapT_len, mapT_len]; omega
    · intro u v
      have hu := u.isLt
      have hv := v.isLt
      have hr' : (wr C.gates (oneEach u (⟨v.val, by omega⟩ : Fin (m+2)))).getD C.output false = A u v :=
        (hrep u ⟨v.val, by omega⟩).trans (dif_pos v.isLt)
      obtain ⟨xB, hxB⟩ : ∃ xB, xB = oneEach u (⟨v.val, by omega⟩ : Fin (m+2)) := ⟨_, rfl⟩
      obtain ⟨x, hx⟩ : ∃ x, x = oneEach u v := ⟨_, rfl⟩
      rw [← hxB] at hr'
      have hxBv : ∀ i, xB.getD i false = decide (i = u.val ∨ i = n + v.val) := by
        intro i; rw [hxB]; exact oneval _ _ _
      have hxv : ∀ i, x.getD i false = decide (i = u.val ∨ i = n + v.val) := by
        intro i; rw [hx]; exact oneval _ _ _
      have hxBl : xB.length = n+m+2 := by rw [hxB, onelen]; omega
      have hxl : x.length = n+m+1 := by rw [hx, onelen]; omega
      have I0 : Inv (D1 zi) zi 1 M (n+m+2) xB x := by
        refine ⟨by omega, by omega, ?_, ?_⟩
        · rw [hxBv]; exact decide_eq_false (by omega)
        · intro i hi hne
          have hd : D1 zi i = i := by unfold D1; rw [if_pos (by omega)]
          rw [hd]
          exact ⟨Or.inl (by omega), by rw [hxBv, hxv]⟩
      have I1 := sim (D1 zi) zi 1 M (n+m+2)
        (by intro i hi; unfold D1; rw [if_neg (by omega)]) (by omega) pre xB x I0 (by omega)
      rw [hxBl] at I1
      obtain ⟨W1, hW1⟩ : ∃ W1, W1 = wr pre xB := ⟨_, rfl⟩
      obtain ⟨W1', hW1'⟩ : ∃ W1', W1' = wr (mapT (D1 zi) zi M pre (n+m+2)) x := ⟨_, rfl⟩
      rw [← hW1, ← hW1'] at I1
      have hW1l : W1.length = t := by rw [hW1, wr_len]; omega
      have hW1'l : W1'.length = n+m+1+pre.length := by rw [hW1', wr_len, mapT_len]; omega
      have sv := sub_val (D1 zi) zi 1 M (n+m+2) W1 W1' I1 (by omega) g hgm.1 hgm.2 hzg
      rw [hW1l, ← hs] at sv
      obtain ⟨val, hval⟩ : ∃ val, val = g.op.eval (g.inputs.map fun i => W1.getD i false) := ⟨_, rfl⟩
      rw [← hval] at sv
      have I2 : Inv (D2 zi t s) zi 2 M (t+1) (W1 ++ [val]) W1' := by
        refine ⟨by rw [List.length_append, List.length_singleton]; omega,
          by rw [List.length_append, List.length_singleton]; omega, ?_, ?_⟩
        · rw [getD_snoc, if_pos (by omega)]; exact I1.2.2.1
        · intro i hi hne
          rw [List.length_append, List.length_singleton] at hi
          by_cases hit : i < t
          · have hd : D2 zi t s i = D1 zi i := by unfold D2; rw [if_pos hit]
            rw [hd, getD_snoc, if_pos (by omega)]
            exact I1.2.2.2 i (by omega) hne
          · have hit' : i = t := by omega
            have hd : D2 zi t s i = s := by unfold D2; rw [if_neg hit, if_pos hit']
            rw [hd, getD_snoc, if_neg (by omega), if_pos (by omega)]
            exact sv
      have I3 := sim (D2 zi t s) zi 2 M (t+1)
        (by intro i hi; unfold D2; rw [if_neg (by omega), if_neg (by omega)]) (by omega)
        post _ _ I2 (by omega)
      rw [List.length_append, List.length_singleton, hW1l] at I3
      have hfin := Inv_sg I3 (by rw [wr_len, mapT_len]; omega) C.output
      have hWfl : (wr post (W1 ++ [val])).length = t+1+post.length := by
        rw [wr_len, List.length_append, List.length_singleton, hW1l]
      rw [hWfl] at hfin
      show (wr (mapT (D1 zi) zi M pre (n+m+2) ++ mapT (D2 zi t s) zi M post (t+1)) (oneEach u v)).getD
        (sg (D2 zi t s) zi M (t+1+post.length) C.output) false = A u v
      rw [← hx, wr_app, ← hW1', hfin.2]
      rw [hsplit, wr_app, wr_cons, ← hW1, ← hval] at hr'
      exact hr'
  · have hread' : ∀ g ∈ C.gates, (n+m+1) ∉ g.inputs := fun g hg hz => hread ⟨g, hg, hz⟩
    obtain ⟨u, v, hc, hv⟩ := hw
    have hu := u.isLt
    have hvl := v.isLt
    have hcl := c.isLt
    have h1' : (wr C.gates (oneEach u (⟨m+1, by omega⟩ : Fin (m+2)))).getD C.output false = true :=
      ((hrep u ⟨m+1, by omega⟩).trans (dif_neg (Nat.lt_irrefl (m+1)))).trans hc
    have h2' : (wr C.gates (oneEach u (⟨v.val, by omega⟩ : Fin (m+2)))).getD C.output false = false :=
      ((hrep u ⟨v.val, by omega⟩).trans (dif_pos v.isLt)).trans hv
    have h3' : (wr C.gates (oneEach u (⟨c.val, by omega⟩ : Fin (m+2)))).getD C.output false = true :=
      ((hrep u ⟨c.val, by omega⟩).trans (dif_pos c.isLt)).trans hc
    by_cases ho : C.output = n+m+1
    · rw [ho, wr_input _ _ _ (by rw [onelen]; omega), oneval] at h3'
      have h4 := of_decide_eq_true h3'
      dsimp only at h4
      omega
    · have := monoZ (n+m+1) C.gates hmono hread'
        (oneEach u (⟨m+1, by omega⟩ : Fin (m+2))) (oneEach u (⟨v.val, by omega⟩ : Fin (m+2)))
        (by rw [onelen, onelen])
        (fun i hi => by
          rw [oneval, oneval]
          intro h
          have h' := of_decide_eq_true h
          dsimp only at h' ⊢
          exact decide_eq_true (by omega)) C.output ho h1'
      rw [h2'] at this
      exact absurd this Bool.false_ne_true

end PEqualNP.Outside.L_lib_1386

open PEqualNP.Outside.L_lib_1386

theorem PEqualNP.Outside.L_lib_1386 :
  ∀ (n m : Nat) (A : Fin n → Fin (m+1) → Bool) (c : Fin (m+1)),
    (∃ (u : Fin n) (v : Fin (m+1)), A u c = true ∧ A u v = false) →
    let B : Fin n → Fin (m+2) → Bool := fun u j =>
      if h : j.val < m+1 then A u ⟨j.val,h⟩ else A u c
    ∀ k : Nat, PEqualNP.Represents.RepSizeAtMost B (k+1) ↔
      PEqualNP.Represents.RepSizeAtMost A k := by
  intro n m A c hw B k
  exact ⟨rev n m A c hw k, fwd n m A c k⟩
