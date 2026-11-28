import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1452_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

inductive SForm (k : Nat) where
  | const (b : Bool)
  | lit (j : Fin k) (pol : Bool)
  | and (l r : SForm k)
  | or (l r : SForm k)

def SForm.eval {k : Nat} (Y : Finset (Fin k)) : SForm k → Bool
  | .const b => b
  | .lit j pol => if pol then decide (j ∈ Y) else !decide (j ∈ Y)
  | .and l r => l.eval Y && r.eval Y
  | .or l r => l.eval Y || r.eval Y

def SForm.neg {k : Nat} : SForm k → SForm k
  | .const b => .const (!b)
  | .lit j pol => .lit j (!pol)
  | .and l r => .or l.neg r.neg
  | .or l r => .and l.neg r.neg

def SForm.posCount {k : Nat} (J : Finset (Fin k)) : SForm k → Nat
  | .const _ => 0
  | .lit j pol => if pol = true ∧ j ∈ J then 1 else 0
  | .and l r => l.posCount J + r.posCount J
  | .or l r => l.posCount J + r.posCount J

def SForm.negCount {k : Nat} (J : Finset (Fin k)) : SForm k → Nat
  | .const _ => 0
  | .lit j pol => if pol = false ∧ j ∈ J then 1 else 0
  | .and l r => l.negCount J + r.negCount J
  | .or l r => l.negCount J + r.negCount J

lemma SForm.eval_neg {k : Nat} (Y : Finset (Fin k)) (F : SForm k) :
    F.neg.eval Y = !(F.eval Y) := by
  induction F with
  | const b => rfl
  | lit j pol => cases pol <;> simp [SForm.neg, SForm.eval]
  | and l r ihl ihr => simp [SForm.neg, SForm.eval, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.eval, ihl, ihr]

lemma SForm.posCount_neg {k : Nat} (J : Finset (Fin k)) (F : SForm k) :
    F.neg.posCount J = F.negCount J := by
  induction F with
  | const b => rfl
  | lit j pol => cases pol <;> simp [SForm.neg, SForm.posCount, SForm.negCount]
  | and l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]

lemma SForm.negCount_neg {k : Nat} (J : Finset (Fin k)) (F : SForm k) :
    F.neg.negCount J = F.posCount J := by
  induction F with
  | const b => rfl
  | lit j pol => cases pol <;> simp [SForm.neg, SForm.posCount, SForm.negCount]
  | and l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]
  | or l r ihl ihr => simp [SForm.neg, SForm.posCount, SForm.negCount, ihl, ihr]

def stepForm {k : Nat} (fs : List (SForm k)) (g : Gate) : SForm k :=
  match g.op with
  | .not => ((g.inputs.head?.map (fun j => fs.getD j (.const false))).getD (.const false)).neg
  | .and => g.inputs.foldl (fun acc j => .and acc (fs.getD j (.const false))) (.const true)
  | .or => g.inputs.foldl (fun acc j => .or acc (fs.getD j (.const false))) (.const false)
  | _ => .const false

lemma foldl_and_eval {k : Nat} (Y : Finset (Fin k)) (fs : List (SForm k))
    (ins : List Nat) (init : SForm k) :
    (ins.foldl (fun acc j => SForm.and acc (fs.getD j (.const false))) init).eval Y =
    (init.eval Y && (ins.map (fun j => (fs.getD j (.const false)).eval Y)).all id) := by
  induction ins generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.all_cons, id_eq, ih, SForm.eval]
    cases init.eval Y <;> cases (fs.getD a (.const false)).eval Y <;> simp

lemma foldl_or_eval {k : Nat} (Y : Finset (Fin k)) (fs : List (SForm k))
    (ins : List Nat) (init : SForm k) :
    (ins.foldl (fun acc j => SForm.or acc (fs.getD j (.const false))) init).eval Y =
    (init.eval Y || (ins.map (fun j => (fs.getD j (.const false)).eval Y)).any id) := by
  induction ins generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.any_cons, id_eq, ih, SForm.eval]
    cases init.eval Y <;> cases (fs.getD a (.const false)).eval Y <;> simp

lemma foldl_and_counts {k : Nat} (J : Finset (Fin k)) (fs : List (SForm k))
    (zs : List (Nat × Nat))
    (hcnt : ∀ i, (fs.getD i (.const false)).posCount J = (zs.getD i (0, 0)).1 ∧
                 (fs.getD i (.const false)).negCount J = (zs.getD i (0, 0)).2)
    (ins : List Nat) (initF : SForm k) (initC : Nat × Nat)
    (hi1 : initF.posCount J = initC.1) (hi2 : initF.negCount J = initC.2) :
    let F := ins.foldl (fun acc j => SForm.and acc (fs.getD j (.const false))) initF
    let C := ins.foldl (fun (acc : Nat × Nat) j =>
      let z := zs.getD j (0, 0); (acc.1 + z.1, acc.2 + z.2)) initC
    F.posCount J = C.1 ∧ F.negCount J = C.2 := by
  induction ins generalizing initF initC with
  | nil => exact ⟨hi1, hi2⟩
  | cons a t ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp only [SForm.posCount, hi1, (hcnt a).1]
    · simp only [SForm.negCount, hi2, (hcnt a).2]

lemma foldl_or_counts {k : Nat} (J : Finset (Fin k)) (fs : List (SForm k))
    (zs : List (Nat × Nat))
    (hcnt : ∀ i, (fs.getD i (.const false)).posCount J = (zs.getD i (0, 0)).1 ∧
                 (fs.getD i (.const false)).negCount J = (zs.getD i (0, 0)).2)
    (ins : List Nat) (initF : SForm k) (initC : Nat × Nat)
    (hi1 : initF.posCount J = initC.1) (hi2 : initF.negCount J = initC.2) :
    let F := ins.foldl (fun acc j => SForm.or acc (fs.getD j (.const false))) initF
    let C := ins.foldl (fun (acc : Nat × Nat) j =>
      let z := zs.getD j (0, 0); (acc.1 + z.1, acc.2 + z.2)) initC
    F.posCount J = C.1 ∧ F.negCount J = C.2 := by
  induction ins generalizing initF initC with
  | nil => exact ⟨hi1, hi2⟩
  | cons a t ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp only [SForm.posCount, hi1, (hcnt a).1]
    · simp only [SForm.negCount, hi2, (hcnt a).2]

lemma getD_append_singleton {α : Type*} (l : List α) (x d : α) (i : Nat) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  simp only [List.getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have hnone : ([x] : List α)[i - l.length]? = none :=
      List.getElem?_eq_none (by simp; omega)
    rw [hnone]; rfl

lemma unfold_circuit {k : Nat} (J : Finset (Fin k)) (D : Circuit) (hfit : FanInTwo D) :
    letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
    ∃ F : SForm k,
      (∀ Y : Finset (Fin k),
        F.eval Y = (D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false, true])).getD D.output false) ∧
      F.posCount J =
        ((D.gates.foldl (fun (zs : List (Nat × Nat)) g =>
          let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
            let z := zs.getD j (0, 0)
            (acc.1 + z.1, acc.2 + z.2)) (0, 0)
          let h := (g.inputs.head?.map (fun j => zs.getD j (0, 0))).getD (0, 0)
          zs ++ [if g.op = GateOp.not then (h.2, h.1) else ab])
          (List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0, 0), (0, 0)])).getD D.output (0, 0)).1 := by
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let stepW : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let stepC : List (Nat × Nat) → Gate → List (Nat × Nat) := fun zs g =>
    let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
      let z := zs.getD j (0, 0)
      (acc.1 + z.1, acc.2 + z.2)) (0, 0)
    let h := (g.inputs.head?.map (fun j => zs.getD j (0, 0))).getD (0, 0)
    zs ++ [if g.op = GateOp.not then (h.2, h.1) else ab]
  let stepF : List (SForm k) → Gate → List (SForm k) := fun fs g =>
    fs ++ [stepForm fs g]
  have hgen : ∀ (gs : List Gate) (fs : List (SForm k)) (zs : List (Nat × Nat))
      (ws : Finset (Fin k) → List Bool),
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) →
      fs.length = zs.length →
      (∀ Y, fs.length = (ws Y).length) →
      (∀ Y i, (fs.getD i (.const false)).eval Y = (ws Y).getD i false) →
      (∀ i, (fs.getD i (.const false)).posCount J = (zs.getD i (0, 0)).1 ∧
            (fs.getD i (.const false)).negCount J = (zs.getD i (0, 0)).2) →
      let fs' := gs.foldl stepF fs
      let zs' := gs.foldl stepC zs
      (∀ Y i, (fs'.getD i (.const false)).eval Y = (gs.foldl stepW (ws Y)).getD i false) ∧
      (∀ i, (fs'.getD i (.const false)).posCount J = (zs'.getD i (0, 0)).1 ∧
            (fs'.getD i (.const false)).negCount J = (zs'.getD i (0, 0)).2) := by
    intro gs
    induction gs with
    | nil =>
      intro fs zs ws _ _ _ hev hcnt
      exact ⟨hev, hcnt⟩
    | cons g rest ih =>
      intro fs zs ws hgs hlen1 hlen2 hev hcnt
      simp only [List.foldl_cons]
      have hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hgs g (by simp)
      have hrest : ∀ g' ∈ rest, g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not :=
        fun g' hg' => hgs g' (by simp [hg'])
      have hstep_ev : ∀ Y, (stepForm fs g).eval Y = g.op.eval (g.inputs.map fun i => (ws Y).getD i false) := by
        intro Y
        rcases hg with hop | hop | hop
        · unfold stepForm
          rw [hop]
          simp only [GateOp.eval]
          rw [foldl_and_eval]
          simp only [SForm.eval, Bool.true_and]
          congr 1
          exact List.map_congr_left (fun i _ => hev Y i)
        · unfold stepForm
          rw [hop]
          simp only [GateOp.eval]
          rw [foldl_or_eval]
          simp only [SForm.eval, Bool.false_or]
          congr 1
          exact List.map_congr_left (fun i _ => hev Y i)
        · unfold stepForm
          rw [hop]
          simp only [GateOp.eval, SForm.eval_neg]
          cases h_in : g.inputs with
          | nil => rfl
          | cons a t =>
            simp only [List.head?_cons, Option.map_some, Option.getD_some, List.map_cons, List.headD_cons]
            rw [hev Y a]
      have hstep_cnt :
          (stepForm fs g).posCount J =
            (if g.op = GateOp.not then
              ((g.inputs.head?.map (fun j => zs.getD j (0, 0))).getD (0, 0)).2
            else
              (g.inputs.foldl (fun (acc : Nat × Nat) j =>
                let z := zs.getD j (0, 0); (acc.1 + z.1, acc.2 + z.2)) (0, 0)).1) ∧
          (stepForm fs g).negCount J =
            (if g.op = GateOp.not then
              ((g.inputs.head?.map (fun j => zs.getD j (0, 0))).getD (0, 0)).1
            else
              (g.inputs.foldl (fun (acc : Nat × Nat) j =>
                let z := zs.getD j (0, 0); (acc.1 + z.1, acc.2 + z.2)) (0, 0)).2) := by
        rcases hg with hop | hop | hop
        · unfold stepForm
          rw [hop]
          simp only [reduceCtorEq, ↓reduceIte]
          exact foldl_and_counts J fs zs hcnt g.inputs (.const true) (0, 0) rfl rfl
        · unfold stepForm
          rw [hop]
          simp only [reduceCtorEq, ↓reduceIte]
          exact foldl_or_counts J fs zs hcnt g.inputs (.const false) (0, 0) rfl rfl
        · unfold stepForm
          rw [hop]
          simp only [↓reduceIte, SForm.posCount_neg, SForm.negCount_neg]
          cases h_in : g.inputs with
          | nil => exact ⟨rfl, rfl⟩
          | cons a t =>
            simp only [List.head?_cons, Option.map_some, Option.getD_some]
            exact ⟨(hcnt a).2, (hcnt a).1⟩
      apply ih (stepF fs g) (stepC zs g) (fun Y => stepW (ws Y) g) hrest
      · simp [stepF, stepC, hlen1]
      · intro Y; simp [stepF, stepW, hlen2 Y]
      · intro Y i
        simp only [stepF, stepW, getD_append_singleton, hlen2 Y]
        by_cases h1 : i < (ws Y).length
        · rw [if_pos h1, if_pos h1]; exact hev Y i
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : i = (ws Y).length
          · rw [if_pos h2, if_pos h2]; exact hstep_ev Y
          · rw [if_neg h2, if_neg h2]; rfl
      · intro i
        simp only [stepF, stepC, getD_append_singleton, hlen1]
        by_cases h1 : i < zs.length
        · rw [if_pos h1, if_pos h1]; exact hcnt i
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : i = zs.length
          · rw [if_pos h2, if_pos h2]
            by_cases hnot : g.op = GateOp.not
            · rw [if_pos hnot]
              have hc1 := hstep_cnt.1
              have hc2 := hstep_cnt.2
              rw [if_pos hnot] at hc1 hc2
              exact ⟨hc1, hc2⟩
            · rw [if_neg hnot]
              have hc1 := hstep_cnt.1
              have hc2 := hstep_cnt.2
              rw [if_neg hnot] at hc1 hc2
              exact ⟨hc1, hc2⟩
          · rw [if_neg h2, if_neg h2]; exact ⟨rfl, rfl⟩
  let fs0 : List (SForm k) := List.ofFn (fun j : Fin k => SForm.lit j true) ++ [.const false, .const true]
  let zs0 : List (Nat × Nat) :=
    List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0, 0), (0, 0)]
  let ws0 : Finset (Fin k) → List Bool := fun Y =>
    List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false, true]
  have hgs : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    intro g hg
    have h := (hfit g hg).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  have hbase := hgen D.gates fs0 zs0 ws0 hgs
    (by simp [fs0, zs0])
    (fun Y => by simp [fs0, ws0])
    (fun Y i => by
      simp only [fs0, ws0, List.getD, List.getElem?_append, List.length_ofFn]
      by_cases h1 : i < k
      · rw [if_pos h1, if_pos h1]
        simp [List.getElem?_ofFn, h1, SForm.eval]
      · rw [if_neg h1, if_neg h1]
        rcases hsub : i - k with _ | _ | m
        · rfl
        · rfl
        · have hf1 : ([SForm.const false, SForm.const true] : List (SForm k))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          have hf2 : ([false, true] : List Bool)[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          rw [hf1, hf2]; rfl)
    (fun i => by
      simp only [fs0, zs0, List.getD, List.getElem?_append, List.length_ofFn]
      by_cases h1 : i < k
      · rw [if_pos h1, if_pos h1]
        simp [List.getElem?_ofFn, h1, SForm.posCount, SForm.negCount]
      · rw [if_neg h1, if_neg h1]
        rcases hsub : i - k with _ | _ | m
        · exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
        · have hf1 : ([SForm.const false, SForm.const true] : List (SForm k))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          have hf2 : ([(0, 0), (0, 0)] : List (Nat × Nat))[m + 2]? = none :=
            List.getElem?_eq_none (Nat.le_add_left 2 m)
          rw [hf1, hf2]; exact ⟨rfl, rfl⟩)
  refine ⟨(D.gates.foldl stepF fs0).getD D.output (.const false), ?_, ?_⟩
  · intro Y
    exact hbase.1 Y D.output
  · exact (hbase.2 D.output).1

def incPairs {k : Nat} (A0 B0 : Finset (Finset (Fin k))) :
    Finset (Finset (Fin k) × Finset (Fin k)) :=
  (A0 ×ˢ B0).filter (fun p => p.1 ⊆ p.2)

noncomputable def khrap {k : Nat} (A0 B0 : Finset (Finset (Fin k))) : ℝ :=
  if A0.card = 0 ∨ B0.card = 0 then 0
  else ((incPairs A0 B0).card : ℝ) ^ 2 / ((A0.card : ℝ) * (B0.card : ℝ))

lemma titu_div {x1 x2 y1 y2 b : ℝ} (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hb : 0 < b)
    (h1 : y1 = 0 → x1 = 0) (h2 : y2 = 0 → x2 = 0) :
    (if y1 + y2 = 0 then (0 : ℝ) else (x1 + x2) ^ 2 / ((y1 + y2) * b)) ≤
    (if y1 = 0 then (0 : ℝ) else x1 ^ 2 / (y1 * b)) +
    (if y2 = 0 then (0 : ℝ) else x2 ^ 2 / (y2 * b)) := by
  by_cases h10 : y1 = 0
  · subst h10
    have hx1 : x1 = 0 := h1 rfl
    subst hx1
    simp
  · by_cases h20 : y2 = 0
    · subst h20
      have hx2 : x2 = 0 := h2 rfl
      subst hx2
      simp
    · have hp1 : 0 < y1 := lt_of_le_of_ne hy1 (Ne.symm h10)
      have hp2 : 0 < y2 := lt_of_le_of_ne hy2 (Ne.symm h20)
      have hp12 : 0 < y1 + y2 := add_pos hp1 hp2
      rw [if_neg (ne_of_gt hp12), if_neg h10, if_neg h20]
      have hden1 : 0 < y1 * b := mul_pos hp1 hb
      have hden2 : 0 < y2 * b := mul_pos hp2 hb
      have hden12 : 0 < (y1 + y2) * b := mul_pos hp12 hb
      rw [div_add_div _ _ (ne_of_gt hden1) (ne_of_gt hden2)]
      rw [div_le_div_iff₀ hden12 (mul_pos hden1 hden2)]
      nlinarith [sq_nonneg (x1 * y2 - x2 * y1), mul_pos hb hb]

lemma card_incPairs_eq_sum_left {k : Nat} (A0 B0 : Finset (Finset (Fin k))) :
    (incPairs A0 B0).card = ∑ S ∈ A0, (B0.filter (fun T => S ⊆ T)).card := by
  classical
  rw [incPairs, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.card_filter]

lemma card_incPairs_eq_sum_right {k : Nat} (A0 B0 : Finset (Finset (Fin k))) :
    (incPairs A0 B0).card = ∑ T ∈ B0, (A0.filter (fun S => S ⊆ T)).card := by
  classical
  rw [incPairs, Finset.card_filter, Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro T _
  rw [Finset.card_filter]

lemma incPairs_disjoint_left {k : Nat} (A1 A2 B0 : Finset (Finset (Fin k)))
    (hdisj : Disjoint A1 A2) :
    (incPairs (A1 ∪ A2) B0).card = (incPairs A1 B0).card + (incPairs A2 B0).card := by
  classical
  rw [card_incPairs_eq_sum_left, Finset.sum_union hdisj, ← card_incPairs_eq_sum_left,
      ← card_incPairs_eq_sum_left]

lemma incPairs_disjoint_right {k : Nat} (A0 B1 B2 : Finset (Finset (Fin k)))
    (hdisj : Disjoint B1 B2) :
    (incPairs A0 (B1 ∪ B2)).card = (incPairs A0 B1).card + (incPairs A0 B2).card := by
  classical
  rw [card_incPairs_eq_sum_right, Finset.sum_union hdisj, ← card_incPairs_eq_sum_right,
      ← card_incPairs_eq_sum_right]

lemma card_superset_filter_le {k : Nat} {J : Finset (Fin k)} {a b : Nat} {j : Fin k}
    {B0 : Finset (Finset (Fin k))} (hB0 : B0 ⊆ J.powersetCard b)
    (hjB : ∀ T ∈ B0, j ∈ T) (hjJ : j ∈ J)
    {S : Finset (Fin k)} (hSJ : S ⊆ J) (hSc : S.card = a) (hjS : j ∉ S) :
    (B0.filter (fun T => S ⊆ T)).card ≤ Nat.choose (J.card - a - 1) (b - a - 1) := by
  classical
  have hle : (B0.filter (fun T => S ⊆ T)).card ≤
      ((J \ insert j S).powersetCard (b - a - 1)).card := by
    apply Finset.card_le_card_of_injOn (fun T => T \ insert j S)
    · intro T hT
      have hTf := Finset.mem_filter.mp hT
      have hTmem := Finset.mem_powersetCard.mp (hB0 hTf.1)
      have hjT : j ∈ T := hjB T hTf.1
      have hinsT : insert j S ⊆ T := Finset.insert_subset_iff.mpr ⟨hjT, hTf.2⟩
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      refine ⟨Finset.sdiff_subset_sdiff hTmem.1 Finset.Subset.rfl, ?_⟩
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hinsT, hTmem.2,
          Finset.card_insert_of_notMem hjS, hSc]
      omega
    · intro T1 hT1 T2 hT2 heq
      dsimp only at heq
      have h1 := Finset.mem_filter.mp hT1
      have h2 := Finset.mem_filter.mp hT2
      have hins1 : insert j S ⊆ T1 := Finset.insert_subset_iff.mpr ⟨hjB T1 h1.1, h1.2⟩
      have hins2 : insert j S ⊆ T2 := Finset.insert_subset_iff.mpr ⟨hjB T2 h2.1, h2.2⟩
      calc T1 = (T1 \ insert j S) ∪ insert j S := (Finset.sdiff_union_of_subset hins1).symm
        _ = (T2 \ insert j S) ∪ insert j S := by rw [heq]
        _ = T2 := Finset.sdiff_union_of_subset hins2
  rw [Finset.card_powersetCard] at hle
  have hinsJ : insert j S ⊆ J := Finset.insert_subset_iff.mpr ⟨hjJ, hSJ⟩
  have hcard : (J \ insert j S).card = J.card - a - 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hinsJ, Finset.card_insert_of_notMem hjS, hSc]
    omega
  rwa [hcard] at hle

lemma card_subset_filter_le {k : Nat} {J : Finset (Fin k)} {a b : Nat} {j : Fin k}
    {A0 : Finset (Finset (Fin k))} (hA0 : A0 ⊆ J.powersetCard a)
    (hjA : ∀ S ∈ A0, j ∉ S)
    {T : Finset (Fin k)} (hTc : T.card = b) (hjT : j ∈ T) :
    (A0.filter (fun S => S ⊆ T)).card ≤ Nat.choose (b - 1) a := by
  classical
  have hsub : A0.filter (fun S => S ⊆ T) ⊆ (T.erase j).powersetCard a := by
    intro S hS
    simp only [Finset.mem_filter] at hS
    have hSmem := Finset.mem_powersetCard.mp (hA0 hS.1)
    rw [Finset.mem_powersetCard]
    refine ⟨?_, hSmem.2⟩
    intro x hx
    rw [Finset.mem_erase]
    exact ⟨fun hxj => hjA S hS.1 (hxj ▸ hx), hS.2 hx⟩
  calc (A0.filter (fun S => S ⊆ T)).card
      ≤ ((T.erase j).powersetCard a).card := Finset.card_le_card hsub
    _ = Nat.choose (T.erase j).card a := Finset.card_powersetCard _ _
    _ = Nat.choose (b - 1) a := by rw [Finset.card_erase_of_mem hjT, hTc]

lemma khrap_bound {k : Nat} (J U : Finset (Fin k)) (hUJ : Disjoint U J)
    (a b : Nat) (hab : a < b) (hbJ : b ≤ J.card) (F : SForm k) :
    ∀ (A0 B0 : Finset (Finset (Fin k))),
      A0 ⊆ J.powersetCard a → B0 ⊆ J.powersetCard b →
      (∀ S ∈ A0, F.eval (U ∪ S) = false) →
      (∀ T ∈ B0, F.eval (U ∪ T) = true) →
      khrap A0 B0 ≤ ((Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a : Nat) : ℝ) *
        (F.posCount J : ℝ) := by
  classical
  induction F with
  | const c =>
    intro A0 B0 _ _ hA hB
    simp only [SForm.posCount, Nat.cast_zero, mul_zero]
    unfold khrap
    by_cases h0 : A0.card = 0 ∨ B0.card = 0
    · rw [if_pos h0]
    · push_neg at h0
      obtain ⟨S, hS⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0.1)
      obtain ⟨T, hT⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0.2)
      have hc1 := hA S hS
      have hc2 := hB T hT
      simp only [SForm.eval] at hc1 hc2
      rw [hc1] at hc2
      exact absurd hc2 (by decide)
  | lit j pol =>
    intro A0 B0 hA0 hB0 hA hB
    by_cases h0 : A0.card = 0 ∨ B0.card = 0
    · unfold khrap
      rw [if_pos h0]
      positivity
    · push_neg at h0
      by_cases hjJ : j ∈ J
      · cases pol with
        | false =>
          have hemp : incPairs A0 B0 = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro p hp
            simp only [incPairs, Finset.mem_filter, Finset.mem_product] at hp
            have h1 := hA p.1 hp.1.1
            have h2 := hB p.2 hp.1.2
            simp only [SForm.eval, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_false',
              Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2
            exact h2 (Finset.union_subset_union_right hp.2 h1)
          unfold khrap
          rw [if_neg (by push_neg; exact h0), hemp, Finset.card_empty]
          simp [SForm.posCount]
        | true =>
          have hjU : j ∉ U := Finset.disjoint_right.mp hUJ hjJ
          have hjA : ∀ S ∈ A0, j ∉ S := by
            intro S hS hjS
            have h1 := hA S hS
            simp [SForm.eval, hjS] at h1
          have hjB : ∀ T ∈ B0, j ∈ T := by
            intro T hT
            have h2 := hB T hT
            simp [SForm.eval, hjU] at h2
            exact h2
          have hE1 : (incPairs A0 B0).card ≤ A0.card * Nat.choose (J.card - a - 1) (b - a - 1) := by
            rw [card_incPairs_eq_sum_left]
            calc ∑ S ∈ A0, (B0.filter (fun T => S ⊆ T)).card
                ≤ ∑ _S ∈ A0, Nat.choose (J.card - a - 1) (b - a - 1) := by
                  apply Finset.sum_le_sum
                  intro S hS
                  have hSm := Finset.mem_powersetCard.mp (hA0 hS)
                  exact card_superset_filter_le hB0 hjB hjJ hSm.1 hSm.2 (hjA S hS)
              _ = A0.card * Nat.choose (J.card - a - 1) (b - a - 1) := by simp
          have hE2 : (incPairs A0 B0).card ≤ B0.card * Nat.choose (b - 1) a := by
            rw [card_incPairs_eq_sum_right]
            calc ∑ T ∈ B0, (A0.filter (fun S => S ⊆ T)).card
                ≤ ∑ _T ∈ B0, Nat.choose (b - 1) a := by
                  apply Finset.sum_le_sum
                  intro T hT
                  have hTm := Finset.mem_powersetCard.mp (hB0 hT)
                  exact card_subset_filter_le hA0 hjA hTm.2 (hjB T hT)
              _ = B0.card * Nat.choose (b - 1) a := by simp
          have hsq : ((incPairs A0 B0).card : ℝ) ^ 2 ≤
              ((A0.card : ℝ) * (B0.card : ℝ)) *
              ((Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a : Nat) : ℝ) := by
            have h1r : ((incPairs A0 B0).card : ℝ) ≤ (A0.card : ℝ) * (Nat.choose (J.card - a - 1) (b - a - 1) : ℝ) := by
              exact_mod_cast hE1
            have h2r : ((incPairs A0 B0).card : ℝ) ≤ (B0.card : ℝ) * (Nat.choose (b - 1) a : ℝ) := by
              exact_mod_cast hE2
            push_cast
            nlinarith [Nat.cast_nonneg (α := ℝ) (incPairs A0 B0).card]
          unfold khrap
          rw [if_neg (by push_neg; exact h0)]
          simp only [SForm.posCount, hjJ, and_self, ↓reduceIte, Nat.cast_one, mul_one]
          have hpos : (0 : ℝ) < (A0.card : ℝ) * (B0.card : ℝ) :=
            mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0.1))
                    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0.2))
          exact (div_le_iff₀ hpos).mpr (by linarith)
      · obtain ⟨S, hS⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0.1)
        obtain ⟨T, hT⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0.2)
        have hSj : j ∉ S := fun h => hjJ ((Finset.mem_powersetCard.mp (hA0 hS)).1 h)
        have hTj : j ∉ T := fun h => hjJ ((Finset.mem_powersetCard.mp (hB0 hT)).1 h)
        have h1 := hA S hS
        have h2 := hB T hT
        simp only [SForm.eval, Finset.mem_union, hSj, hTj, or_false] at h1 h2
        rw [h1] at h2
        exact absurd h2 (by decide)
  | and l r ihl ihr =>
    intro A0 B0 hA0 hB0 hA hB
    let A1 := A0.filter (fun S => l.eval (U ∪ S) = false)
    let A2 := A0.filter (fun S => l.eval (U ∪ S) = true)
    have hdisj : Disjoint A1 A2 := by
      rw [Finset.disjoint_left]
      intro S h1 h2
      simp only [A1, A2, Finset.mem_filter] at h1 h2
      rw [h1.2] at h2
      exact absurd h2.2 (by decide)
    have hunion : A1 ∪ A2 = A0 := by
      ext S
      simp only [A1, A2, Finset.mem_union, Finset.mem_filter]
      cases l.eval (U ∪ S) <;> simp
    have hA1sub : A1 ⊆ J.powersetCard a := Finset.Subset.trans (Finset.filter_subset _ _) hA0
    have hA2sub : A2 ⊆ J.powersetCard a := Finset.Subset.trans (Finset.filter_subset _ _) hA0
    have hA1l : ∀ S ∈ A1, l.eval (U ∪ S) = false := fun S hS => (Finset.mem_filter.mp hS).2
    have hA2r : ∀ S ∈ A2, r.eval (U ∪ S) = false := by
      intro S hS
      have hSm := Finset.mem_filter.mp hS
      have h := hA S hSm.1
      simp [SForm.eval, hSm.2] at h
      exact h
    have hBl : ∀ T ∈ B0, l.eval (U ∪ T) = true := by
      intro T hT
      have h := hB T hT
      simp [SForm.eval] at h
      exact h.1
    have hBr : ∀ T ∈ B0, r.eval (U ∪ T) = true := by
      intro T hT
      have h := hB T hT
      simp [SForm.eval] at h
      exact h.2
    have hstep : khrap A0 B0 ≤ khrap A1 B0 + khrap A2 B0 := by
      by_cases hB0e : B0.card = 0
      · simp [khrap, hB0e]
      · have hBpos : (0 : ℝ) < (B0.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hB0e)
        have hcardA : (A0.card : ℝ) = (A1.card : ℝ) + (A2.card : ℝ) := by
          rw [← hunion, Finset.card_union_of_disjoint hdisj]; push_cast; rfl
        have hcardE : ((incPairs A0 B0).card : ℝ) =
            ((incPairs A1 B0).card : ℝ) + ((incPairs A2 B0).card : ℝ) := by
          rw [← hunion, incPairs_disjoint_left A1 A2 B0 hdisj]; push_cast; rfl
        have ht := titu_div (x1 := (incPairs A1 B0).card) (x2 := (incPairs A2 B0).card)
          (y1 := A1.card) (y2 := A2.card) (b := B0.card)
          (Nat.cast_nonneg _) (Nat.cast_nonneg _) hBpos
          (fun h => by
            have h0 : A1.card = 0 := Nat.cast_eq_zero.mp h
            rw [Finset.card_eq_zero.mp h0]; simp [incPairs])
          (fun h => by
            have h0 : A2.card = 0 := Nat.cast_eq_zero.mp h
            rw [Finset.card_eq_zero.mp h0]; simp [incPairs])
        rw [← hcardA, ← hcardE] at ht
        have heq0 : khrap A0 B0 =
            if (A0.card : ℝ) = 0 then 0 else ((incPairs A0 B0).card : ℝ) ^ 2 / ((A0.card : ℝ) * (B0.card : ℝ)) := by
          unfold khrap; simp [hB0e]
        have heq1 : khrap A1 B0 =
            if (A1.card : ℝ) = 0 then 0 else ((incPairs A1 B0).card : ℝ) ^ 2 / ((A1.card : ℝ) * (B0.card : ℝ)) := by
          unfold khrap; simp [hB0e]
        have heq2 : khrap A2 B0 =
            if (A2.card : ℝ) = 0 then 0 else ((incPairs A2 B0).card : ℝ) ^ 2 / ((A2.card : ℝ) * (B0.card : ℝ)) := by
          unfold khrap; simp [hB0e]
        rw [heq0, heq1, heq2]
        exact ht
    have h1 := ihl A1 B0 hA1sub hB0 hA1l hBl
    have h2 := ihr A2 B0 hA2sub hB0 hA2r hBr
    simp only [SForm.posCount, Nat.cast_add, mul_add]
    linarith
  | or l r ihl ihr =>
    intro A0 B0 hA0 hB0 hA hB
    let B1 := B0.filter (fun T => l.eval (U ∪ T) = true)
    let B2 := B0.filter (fun T => l.eval (U ∪ T) = false)
    have hdisj : Disjoint B1 B2 := by
      rw [Finset.disjoint_left]
      intro T h1 h2
      simp only [B1, B2, Finset.mem_filter] at h1 h2
      rw [h1.2] at h2
      exact absurd h2.2 (by decide)
    have hunion : B1 ∪ B2 = B0 := by
      ext T
      simp only [B1, B2, Finset.mem_union, Finset.mem_filter]
      cases l.eval (U ∪ T) <;> simp
    have hB1sub : B1 ⊆ J.powersetCard b := Finset.Subset.trans (Finset.filter_subset _ _) hB0
    have hB2sub : B2 ⊆ J.powersetCard b := Finset.Subset.trans (Finset.filter_subset _ _) hB0
    have hB1l : ∀ T ∈ B1, l.eval (U ∪ T) = true := fun T hT => (Finset.mem_filter.mp hT).2
    have hB2r : ∀ T ∈ B2, r.eval (U ∪ T) = true := by
      intro T hT
      have hTm := Finset.mem_filter.mp hT
      have h := hB T hTm.1
      simp [SForm.eval, hTm.2] at h
      exact h
    have hAl : ∀ S ∈ A0, l.eval (U ∪ S) = false := by
      intro S hS
      have h := hA S hS
      simp [SForm.eval] at h
      exact h.1
    have hAr : ∀ S ∈ A0, r.eval (U ∪ S) = false := by
      intro S hS
      have h := hA S hS
      simp [SForm.eval] at h
      exact h.2
    have hstep : khrap A0 B0 ≤ khrap A0 B1 + khrap A0 B2 := by
      by_cases hA0e : A0.card = 0
      · simp [khrap, hA0e]
      · have hApos : (0 : ℝ) < (A0.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hA0e)
        have hcardB : (B0.card : ℝ) = (B1.card : ℝ) + (B2.card : ℝ) := by
          rw [← hunion, Finset.card_union_of_disjoint hdisj]; push_cast; rfl
        have hcardE : ((incPairs A0 B0).card : ℝ) =
            ((incPairs A0 B1).card : ℝ) + ((incPairs A0 B2).card : ℝ) := by
          rw [← hunion, incPairs_disjoint_right A0 B1 B2 hdisj]; push_cast; rfl
        have ht := titu_div (x1 := (incPairs A0 B1).card) (x2 := (incPairs A0 B2).card)
          (y1 := B1.card) (y2 := B2.card) (b := A0.card)
          (Nat.cast_nonneg _) (Nat.cast_nonneg _) hApos
          (fun h => by
            have h0 : B1.card = 0 := Nat.cast_eq_zero.mp h
            rw [Finset.card_eq_zero.mp h0]; simp [incPairs])
          (fun h => by
            have h0 : B2.card = 0 := Nat.cast_eq_zero.mp h
            rw [Finset.card_eq_zero.mp h0]; simp [incPairs])
        rw [← hcardB, ← hcardE] at ht
        have heq0 : khrap A0 B0 =
            if (B0.card : ℝ) = 0 then 0 else ((incPairs A0 B0).card : ℝ) ^ 2 / ((B0.card : ℝ) * (A0.card : ℝ)) := by
          unfold khrap; simp [hA0e, mul_comm]
        have heq1 : khrap A0 B1 =
            if (B1.card : ℝ) = 0 then 0 else ((incPairs A0 B1).card : ℝ) ^ 2 / ((B1.card : ℝ) * (A0.card : ℝ)) := by
          unfold khrap; simp [hA0e, mul_comm]
        have heq2 : khrap A0 B2 =
            if (B2.card : ℝ) = 0 then 0 else ((incPairs A0 B2).card : ℝ) ^ 2 / ((B2.card : ℝ) * (A0.card : ℝ)) := by
          unfold khrap; simp [hA0e, mul_comm]
        rw [heq0, heq1, heq2]
        exact ht
    have h1 := ihl A0 B1 hA0 hB1sub hAl hB1l
    have h2 := ihr A0 B2 hA0 hB2sub hAr hB2r
    simp only [SForm.posCount, Nat.cast_add, mul_add]
    linarith

lemma card_incPairs_full_right {k : Nat} (J : Finset (Fin k)) (a b : Nat) :
    (incPairs (J.powersetCard a) (J.powersetCard b)).card =
    Nat.choose J.card b * Nat.choose b a := by
  classical
  rw [card_incPairs_eq_sum_right]
  have hsum : ∑ T ∈ J.powersetCard b, ((J.powersetCard a).filter (fun S => S ⊆ T)).card =
      ∑ _T ∈ J.powersetCard b, Nat.choose b a := by
    apply Finset.sum_congr rfl
    intro T hT
    have hTm := Finset.mem_powersetCard.mp hT
    have heq : (J.powersetCard a).filter (fun S => S ⊆ T) = T.powersetCard a := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨fun ⟨⟨_, hSc⟩, hST⟩ => ⟨hST, hSc⟩, fun ⟨hST, hSc⟩ => ⟨⟨Finset.Subset.trans hST hTm.1, hSc⟩, hST⟩⟩
    rw [heq, Finset.card_powersetCard, hTm.2]
  rw [hsum, Finset.sum_const, smul_eq_mul, Finset.card_powersetCard]

lemma card_incPairs_full_left {k : Nat} (J : Finset (Fin k)) (a b : Nat) (hab : a ≤ b) :
    (incPairs (J.powersetCard a) (J.powersetCard b)).card =
    Nat.choose J.card a * Nat.choose (J.card - a) (b - a) := by
  classical
  rw [card_incPairs_eq_sum_left]
  have hsum : ∑ S ∈ J.powersetCard a, ((J.powersetCard b).filter (fun T => S ⊆ T)).card =
      ∑ _S ∈ J.powersetCard a, Nat.choose (J.card - a) (b - a) := by
    apply Finset.sum_congr rfl
    intro S hS
    have hSm := Finset.mem_powersetCard.mp hS
    have hbij : ((J.powersetCard b).filter (fun T => S ⊆ T)).card =
        ((J \ S).powersetCard (b - a)).card := by
      apply Finset.card_bij (fun T _ => T \ S)
      · intro T hT
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
        refine ⟨Finset.sdiff_subset_sdiff hT.1.1 Finset.Subset.rfl, ?_⟩
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT.2, hT.1.2, hSm.2]
      · intro T1 hT1 T2 hT2 heq
        simp only [Finset.mem_filter] at hT1 hT2
        calc T1 = (T1 \ S) ∪ S := (Finset.sdiff_union_of_subset hT1.2).symm
          _ = (T2 \ S) ∪ S := by rw [heq]
          _ = T2 := Finset.sdiff_union_of_subset hT2.2
      · intro R hR
        rw [Finset.mem_powersetCard] at hR
        have hdisj : Disjoint R S := Finset.disjoint_of_subset_left hR.1 Finset.sdiff_disjoint
        refine ⟨R ∪ S, ?_, Finset.union_sdiff_cancel_right hdisj⟩
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨Finset.union_subset (Finset.Subset.trans hR.1 Finset.sdiff_subset) hSm.1, ?_⟩,
                Finset.subset_union_right⟩
        rw [Finset.card_union_of_disjoint hdisj, hR.2, hSm.2]
        omega
    rw [hbij, Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr hSm.1, hSm.2]
  rw [hsum, Finset.sum_const, smul_eq_mul, Finset.card_powersetCard]

lemma choose_mul_sub_eq {n r : Nat} (hr : 1 ≤ r) (hrn : r ≤ n) :
    r * Nat.choose n r = n * Nat.choose (n - 1) (r - 1) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hrn
  have h2 := Nat.choose_mul_factorial_mul_factorial (show r - 1 ≤ n - 1 by omega)
  have hr_eq : r = (r - 1) + 1 := by omega
  have hn_eq : n = (n - 1) + 1 := by omega
  have hsub : n - 1 - (r - 1) = n - r := by omega
  rw [hsub] at h2
  have hfac_r : Nat.factorial r = r * Nat.factorial (r - 1) := by
    conv_lhs => rw [hr_eq]
    rw [Nat.factorial_succ, ← hr_eq]
  have hfac_n : Nat.factorial n = n * Nat.factorial (n - 1) := by
    conv_lhs => rw [hn_eq]
    rw [Nat.factorial_succ, ← hn_eq]
  have hpos : 0 < Nat.factorial (r - 1) * Nat.factorial (n - r) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hmul : r * Nat.choose n r * (Nat.factorial (r - 1) * Nat.factorial (n - r)) =
      n * Nat.choose (n - 1) (r - 1) * (Nat.factorial (r - 1) * Nat.factorial (n - r)) := by
    calc r * Nat.choose n r * (Nat.factorial (r - 1) * Nat.factorial (n - r))
        = Nat.choose n r * (r * Nat.factorial (r - 1)) * Nat.factorial (n - r) := by ring
      _ = Nat.choose n r * Nat.factorial r * Nat.factorial (n - r) := by rw [← hfac_r]
      _ = Nat.factorial n := h1
      _ = n * Nat.factorial (n - 1) := hfac_n
      _ = n * (Nat.choose (n - 1) (r - 1) * Nat.factorial (r - 1) * Nat.factorial (n - r)) := by rw [← h2]
      _ = n * Nat.choose (n - 1) (r - 1) * (Nat.factorial (r - 1) * Nat.factorial (n - r)) := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

lemma choose_mul_compl_eq {b a : Nat} (hab : a < b) :
    (b - a) * Nat.choose b a = b * Nat.choose (b - 1) a := by
  have h1 : Nat.choose b a = Nat.choose b (b - a) := (Nat.choose_symm (le_of_lt hab)).symm
  have h2 : Nat.choose (b - 1) a = Nat.choose (b - 1) (b - 1 - a) :=
    (Nat.choose_symm (by omega)).symm
  have h3 : b - 1 - a = (b - a) - 1 := by omega
  rw [h1, h2, h3]
  exact choose_mul_sub_eq (by omega) (by omega)

end PEqualNP.Outside.L_lib_1452_aux

theorem PEqualNP.Outside.L_lib_1452 : (letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
let valid := fun (k : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.FanInTwo D ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) D ∧ D.output < k+2+D.size
let run := fun {k : Nat} (D : PEqualNP.CircuitLowerBounds.Circuit) (Y : Finset (Fin k)) =>
  ((D.wires (List.ofFn (fun j : Fin k => decide (j ∈ Y)) ++ [false,true])).getD D.output false)
let pos := fun {k : Nat} (J : Finset (Fin k)) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
  let xs := List.ofFn (fun j : Fin k => ((if j ∈ J then 1 else 0, 0) : Nat × Nat)) ++ [(0,0),(0,0)]
  let ws := D.gates.foldl (fun (zs : List (Nat × Nat)) g =>
    let ab := g.inputs.foldl (fun (acc : Nat × Nat) j =>
      let z := zs.getD j (0,0)
      (acc.1+z.1,acc.2+z.2)) (0,0)
    let h := (g.inputs.head?.map (fun j => zs.getD j (0,0))).getD (0,0)
    zs ++ [if g.op=PEqualNP.CircuitLowerBounds.GateOp.not then (h.2,h.1) else ab]) xs
  (ws.getD D.output (0,0)).1
∀ (k l h : Nat) (A B : Finset (Fin k)) (D : PEqualNP.CircuitLowerBounds.Circuit),
  A ⊆ B → l<h → h ≤ (B \ A).card → valid k D →
  (∀ Y, A ⊆ Y → Y ⊆ B → (((Y \ A).card=l → run D Y=false) ∧ ((Y \ A).card=h → run D Y=true))) →
  ∀ J ⊆ B \ A, ∀ z : Nat, z ≤ (B \ A).card-J.card → z ≤ l → h ≤ z+J.card →
    (h-z)*(J.card-(l-z)) ≤ (h-l)^2 * pos J D) := by
  intro valid run pos k l h A B D hAB hlh hhBA hval hrun J hJ z hz_le hzl hh_le
  obtain ⟨F, hFeval, hFpos⟩ := PEqualNP.Outside.L_lib_1452_aux.unfold_circuit J D hval.1
  have hBA_eq : @sdiff (Finset (Fin k)) (@Finset.instSDiff (Fin k) (fun a b => Classical.propDecidable (a = b))) B A = B \ A := by
    convert rfl
  rw [hBA_eq] at hhBA hJ hz_le
  have hz_card : z ≤ ((B \ A) \ J).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hJ]
    exact hz_le
  obtain ⟨Z, hZsub, hZcard⟩ := Finset.exists_subset_card_eq hz_card
  let U : Finset (Fin k) := A ∪ Z
  have hAJ : Disjoint A J := Finset.disjoint_of_subset_right hJ Finset.disjoint_sdiff
  have hZJ : Disjoint Z J := Finset.disjoint_of_subset_left hZsub Finset.sdiff_disjoint
  have hUJ : Disjoint U J := Finset.disjoint_union_left.mpr ⟨hAJ, hZJ⟩
  have hAZ : Disjoint A Z :=
    Finset.disjoint_of_subset_right (Finset.Subset.trans hZsub Finset.sdiff_subset) Finset.disjoint_sdiff
  let a := l - z
  let b := h - z
  have hab : a < b := by omega
  have hbJ : b ≤ J.card := by omega
  have haJ : a ≤ J.card := le_of_lt (lt_of_lt_of_le hab hbJ)
  let A0 := J.powersetCard a
  let B0 := J.powersetCard b
  have hA0eval : ∀ S ∈ A0, F.eval (U ∪ S) = false := by
    intro S hS
    have hSm := Finset.mem_powersetCard.mp hS
    rw [hFeval]
    have hYsubA : A ⊆ U ∪ S := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
    have hYsubB : U ∪ S ⊆ B := by
      refine Finset.union_subset (Finset.union_subset hAB ?_) ?_
      · exact Finset.Subset.trans hZsub (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
      · exact Finset.Subset.trans hSm.1 (Finset.Subset.trans hJ Finset.sdiff_subset)
    have hcard : ((U ∪ S) \ A).card = l := by
      have hAS : Disjoint A S := Finset.disjoint_of_subset_right hSm.1 hAJ
      have hZS : Disjoint Z S := Finset.disjoint_of_subset_right hSm.1 hZJ
      have heq : (U ∪ S) \ A = Z ∪ S := by
        calc (U ∪ S) \ A = (A ∪ (Z ∪ S)) \ A := by rw [Finset.union_assoc]
          _ = Z ∪ S := Finset.union_sdiff_cancel_left (Finset.disjoint_union_right.mpr ⟨hAZ, hAS⟩)
      rw [heq, Finset.card_union_of_disjoint hZS, hZcard, hSm.2]
      omega
    exact (hrun (U ∪ S) hYsubA hYsubB).1 (by convert hcard)
  have hB0eval : ∀ T ∈ B0, F.eval (U ∪ T) = true := by
    intro T hT
    have hTm := Finset.mem_powersetCard.mp hT
    rw [hFeval]
    have hYsubA : A ⊆ U ∪ T := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
    have hYsubB : U ∪ T ⊆ B := by
      refine Finset.union_subset (Finset.union_subset hAB ?_) ?_
      · exact Finset.Subset.trans hZsub (Finset.Subset.trans Finset.sdiff_subset Finset.sdiff_subset)
      · exact Finset.Subset.trans hTm.1 (Finset.Subset.trans hJ Finset.sdiff_subset)
    have hcard : ((U ∪ T) \ A).card = h := by
      have hAT : Disjoint A T := Finset.disjoint_of_subset_right hTm.1 hAJ
      have hZT : Disjoint Z T := Finset.disjoint_of_subset_right hTm.1 hZJ
      have heq : (U ∪ T) \ A = Z ∪ T := by
        calc (U ∪ T) \ A = (A ∪ (Z ∪ T)) \ A := by rw [Finset.union_assoc]
          _ = Z ∪ T := Finset.union_sdiff_cancel_left (Finset.disjoint_union_right.mpr ⟨hAZ, hAT⟩)
      rw [heq, Finset.card_union_of_disjoint hZT, hZcard, hTm.2]
      omega
    exact (hrun (U ∪ T) hYsubA hYsubB).2 (by convert hcard)
  have hkh := PEqualNP.Outside.L_lib_1452_aux.khrap_bound J U hUJ a b hab hbJ F A0 B0
    Finset.Subset.rfl Finset.Subset.rfl hA0eval hB0eval
  have hA0c : A0.card = Nat.choose J.card a := Finset.card_powersetCard _ _
  have hB0c : B0.card = Nat.choose J.card b := Finset.card_powersetCard _ _
  have hA0pos : 0 < A0.card := by rw [hA0c]; exact Nat.choose_pos haJ
  have hB0pos : 0 < B0.card := by rw [hB0c]; exact Nat.choose_pos hbJ
  have hEL := PEqualNP.Outside.L_lib_1452_aux.card_incPairs_full_left J a b (le_of_lt hab)
  have hER := PEqualNP.Outside.L_lib_1452_aux.card_incPairs_full_right J a b
  have hkh_eq : PEqualNP.Outside.L_lib_1452_aux.khrap A0 B0 =
      ((Nat.choose (J.card - a) (b - a) * Nat.choose b a : Nat) : ℝ) := by
    unfold PEqualNP.Outside.L_lib_1452_aux.khrap
    rw [if_neg (by push_neg; exact ⟨ne_of_gt hA0pos, ne_of_gt hB0pos⟩)]
    have hA0r : (0 : ℝ) < (A0.card : ℝ) := Nat.cast_pos.mpr hA0pos
    have hB0r : (0 : ℝ) < (B0.card : ℝ) := Nat.cast_pos.mpr hB0pos
    rw [div_eq_iff (ne_of_gt (mul_pos hA0r hB0r))]
    have hsq : (PEqualNP.Outside.L_lib_1452_aux.incPairs A0 B0).card ^ 2 =
        Nat.choose (J.card - a) (b - a) * Nat.choose b a * (A0.card * B0.card) := by
      rw [sq, hA0c, hB0c]
      calc (PEqualNP.Outside.L_lib_1452_aux.incPairs A0 B0).card *
           (PEqualNP.Outside.L_lib_1452_aux.incPairs A0 B0).card
          = (Nat.choose J.card a * Nat.choose (J.card - a) (b - a)) *
            (Nat.choose J.card b * Nat.choose b a) := congrArg₂ (· * ·) hEL hER
        _ = Nat.choose (J.card - a) (b - a) * Nat.choose b a *
            (Nat.choose J.card a * Nat.choose J.card b) := by ring
    exact_mod_cast hsq
  rw [hkh_eq] at hkh
  have hnat : Nat.choose (J.card - a) (b - a) * Nat.choose b a ≤
      Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a * F.posCount J := by
    exact_mod_cast hkh
  have hid1 := PEqualNP.Outside.L_lib_1452_aux.choose_mul_sub_eq
    (n := J.card - a) (r := b - a) (by omega) (by omega)
  have hid2 := PEqualNP.Outside.L_lib_1452_aux.choose_mul_compl_eq hab
  have hmul : (b - a) ^ 2 * (Nat.choose (J.card - a) (b - a) * Nat.choose b a) =
      b * (J.card - a) * (Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a) := by
    calc (b - a) ^ 2 * (Nat.choose (J.card - a) (b - a) * Nat.choose b a)
        = ((b - a) * Nat.choose (J.card - a) (b - a)) * ((b - a) * Nat.choose b a) := by ring
      _ = ((J.card - a) * Nat.choose (J.card - a - 1) (b - a - 1)) *
          (b * Nat.choose (b - 1) a) := by rw [hid1, hid2]
      _ = b * (J.card - a) * (Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a) := by ring
  have hCpos : 0 < Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a :=
    Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  have hle2 : b * (J.card - a) * (Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a) ≤
      (b - a) ^ 2 * F.posCount J * (Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a) := by
    calc b * (J.card - a) * (Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a)
        = (b - a) ^ 2 * (Nat.choose (J.card - a) (b - a) * Nat.choose b a) := hmul.symm
      _ ≤ (b - a) ^ 2 * (Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a * F.posCount J) :=
          Nat.mul_le_mul_left _ hnat
      _ = (b - a) ^ 2 * F.posCount J *
          (Nat.choose (J.card - a - 1) (b - a - 1) * Nat.choose (b - 1) a) := by ring
  have hfinal : b * (J.card - a) ≤ (b - a) ^ 2 * F.posCount J :=
    Nat.le_of_mul_le_mul_right hle2 hCpos
  have hba : b - a = h - l := by omega
  rw [hba, hFpos] at hfinal
  exact hfinal
