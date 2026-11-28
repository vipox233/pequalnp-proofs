import PEqualNP.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_53203

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (x : List Bool) (g : List Gate) (w : ℕ) : Bool :=
  ((⟨g, 0⟩ : Circuit).wires x).getD w false

def Ok (n : ℕ) (g : List Gate) : Prop :=
  (∀ h ∈ g, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) ∧
  (∀ j (hj : j < g.length), ∀ i ∈ (g[j]).inputs, i < n + j)

def Ext (n : ℕ) (g g' : List Gate) : Prop :=
  Ok n g' ∧ g.length ≤ g'.length ∧ ∀ x : List Bool, x.length = n → ∀ w < n + g.length, val x g' w = val x g w

lemma wires_snoc (x : List Bool) (g : List Gate) (h : Gate) :
    (⟨g ++ [h], 0⟩ : Circuit).wires x =
      (⟨g, 0⟩ : Circuit).wires x ++ [h.op.eval (h.inputs.map fun i => val x g i)] := by
  simp [Circuit.wires, val, List.foldl_append]

lemma wires_length (x : List Bool) (g : List Gate) : ((⟨g, 0⟩ : Circuit).wires x).length = x.length + g.length := by
  induction g using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton g h ih => rw [wires_snoc]; simp [ih]; omega

lemma Ext.refl {n g} (h : Ok n g) : Ext n g g := ⟨h, le_rfl, fun _ _ _ _ => rfl⟩

lemma Ext.trans {n g g' g''} (a : Ext n g g') (b : Ext n g' g'') : Ext n g g'' :=
  ⟨b.1, a.2.1.trans b.2.1, fun x hx w hw => by
    rw [b.2.2 x hx w (by have := a.2.1; omega), a.2.2 x hx w hw]⟩

lemma add_gate {n g} (hg : Ok n g) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ)
    (ha : a < n + g.length) (hb : b < n + g.length) :
    Ext n g (g ++ [⟨op, [a, b]⟩]) ∧ n + g.length < n + (g ++ [(⟨op, [a, b]⟩ : Gate)]).length ∧
      ∀ x : List Bool, x.length = n → val x (g ++ [⟨op, [a, b]⟩]) (n + g.length) = op.eval [val x g a, val x g b] := by
  refine ⟨⟨⟨?_, ?_⟩, by simp, ?_⟩, by simp, ?_⟩
  · intro h hh
    rcases List.mem_append.1 hh with hh | hh
    · exact hg.1 h hh
    · rw [List.mem_singleton.1 hh]; exact ⟨hop, by simp⟩
  · intro j hj i hi
    by_cases hlt : j < g.length
    · rw [List.getElem_append_left hlt] at hi
      exact hg.2 j hlt i hi
    · have : j = g.length := by simp at hj; omega
      subst this
      simp at hi
      rcases hi with rfl | rfl <;> assumption
  · intro x hx w hw
    unfold val
    rw [wires_snoc, List.getD_append _ _ _ _ (by rw [wires_length, hx]; exact hw)]
  · intro x hx
    have hl : ((⟨g, 0⟩ : Circuit).wires x).length = n + g.length := by rw [wires_length, hx]
    unfold val
    rw [wires_snoc, List.getD_append_right _ _ _ _ (by rw [hl])]
    simp [hl, val]

lemma chain_and {n g} (hg : Ok n g) (acc : ℕ) (l : List ℕ) (ha : acc < n + g.length) (hl : ∀ i ∈ l, i < n) :
    ∃ g' w, Ext n g g' ∧ w < n + g'.length ∧
      ∀ x : List Bool, x.length = n → val x g' w = (val x g acc && l.all (fun i => val x g i)) := by
  induction l generalizing g acc with
  | nil => exact ⟨g, acc, Ext.refl hg, ha, fun x _ => by simp⟩
  | cons i l ih =>
    have hi : i < n + g.length := by have := hl i (by simp); omega
    obtain ⟨e, hw, hv⟩ := add_gate hg GateOp.and (Or.inl rfl) acc i ha hi
    obtain ⟨g', w, e', hw', hv'⟩ := ih e.1 (n + g.length) hw (fun j hj => hl j (by simp [hj]))
    refine ⟨g', w, e.trans e', hw', fun x hx => ?_⟩
    rw [hv' x hx, hv x hx]
    have : l.all (fun j => val x (g ++ [⟨GateOp.and, [acc, i]⟩]) j) = l.all (fun j => val x g j) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      constructor <;> intro H j hj
      · rw [← e.2.2 x hx j (by have := hl j (by simp [hj]); omega)]; exact H j hj
      · rw [e.2.2 x hx j (by have := hl j (by simp [hj]); omega)]; exact H j hj
    rw [this]
    simp [GateOp.eval, Bool.and_assoc]

def dnf (x : List Bool) (T : List (List ℕ)) : Bool := T.any (fun t => t.all (fun i => x.getD i false))

lemma val_input (x : List Bool) (g : List Gate) (i : ℕ) (hi : i < x.length) : val x g i = x.getD i false := by
  induction g using List.reverseRecOn with
  | nil => simp [val, Circuit.wires]
  | append_singleton g h ih =>
    unfold val at ih ⊢
    rw [wires_snoc, List.getD_append _ _ _ _ (by rw [wires_length]; omega)]
    exact ih

lemma build_dnf {n g} (hg : Ok n g) (f t : ℕ) (hf : f < n) (ht : t < n) (T : List (List ℕ))
    (hT : ∀ term ∈ T, ∀ i ∈ term, i < n) :
    ∃ g' w, Ext n g g' ∧ w < n + g'.length ∧
      ∀ x : List Bool, x.length = n → x.getD f false = false → x.getD t false = true → val x g' w = dnf x T := by
  induction T generalizing g with
  | nil =>
    refine ⟨g, f, Ext.refl hg, by omega, fun x hx h0 _ => ?_⟩
    rw [val_input x g f (by omega), h0]; simp [dnf]
  | cons term T ih =>
    obtain ⟨g1, r, e1, hr, hv1⟩ := ih hg (fun s hs => hT s (by simp [hs]))
    obtain ⟨g2, a, e2, ha, hv2⟩ := chain_and e1.1 t term (by omega) (hT term (by simp))
    have hr2 : r < n + g2.length := by have := e2.2.1; omega
    obtain ⟨e3, hw, hv3⟩ := add_gate e2.1 GateOp.or (Or.inr rfl) a r ha hr2
    refine ⟨_, _, (e1.trans e2).trans e3, hw, fun x hx h0 h1 => ?_⟩
    have hterm : term.all (fun i => val x g1 i) = term.all (fun i => x.getD i false) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      constructor <;> intro H i hi
      · rw [← val_input x g1 i (by have := hT term (by simp) i hi; omega)]; exact H i hi
      · rw [val_input x g1 i (by have := hT term (by simp) i hi; omega)]; exact H i hi
    rw [hv3 x hx, hv2 x hx, e2.2.2 x hx r hr, hv1 x hx h0 h1, hterm, val_input x g1 t (by omega), h1]
    simp [GateOp.eval, dnf]

lemma build_many {n} (f t : ℕ) (hf : f < n) (ht : t < n) : ∀ (k : ℕ) (T : Fin k → List (List ℕ)),
    (∀ j, ∀ term ∈ T j, ∀ i ∈ term, i < n) → ∀ g, Ok n g →
    ∃ g' : List Gate, ∃ o : Fin k → ℕ, Ext n g g' ∧ (∀ j, o j < n + g'.length) ∧
      ∀ x : List Bool, x.length = n → x.getD f false = false → x.getD t false = true → ∀ j, val x g' (o j) = dnf x (T j) := by
  intro k
  induction k with
  | zero =>
    intro T _ g hg
    exact ⟨g, fun j => j.elim0, Ext.refl hg, fun j => j.elim0, fun _ _ _ _ j => j.elim0⟩
  | succ k ih =>
    intro T hT g hg
    obtain ⟨g1, w, e1, hw, hv1⟩ := build_dnf hg f t hf ht (T 0) (hT 0)
    obtain ⟨g2, o, e2, ho, hv2⟩ := ih (fun j => T j.succ) (fun j => hT j.succ) g1 e1.1
    refine ⟨g2, Fin.cases w o, e1.trans e2, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · have := e2.2.1; simp; omega
      · simpa using ho j
    · intro x hx h0 h1 j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cases_zero]
        rw [e2.2.2 x hx w hw, hv1 x hx h0 h1]
      · simpa using hv2 x hx h0 h1 j

lemma circuit_mono (g : List Gate) (hg : ∀ h ∈ g, (h.op = GateOp.and ∨ h.op = GateOp.or))
    (x y : List Bool) (hl : x.length = y.length) (hxy : ∀ w, x.getD w false = true → y.getD w false = true) :
    ∀ w, val x g w = true → val y g w = true := by
  induction g using List.reverseRecOn with
  | nil => simpa [val, Circuit.wires] using hxy
  | append_singleton g h ih =>
    have ih' := ih (fun k hk => hg k (by simp [hk]))
    intro w hw
    have lx : ((⟨g, 0⟩ : Circuit).wires x).length = x.length + g.length := wires_length x g
    have ly : ((⟨g, 0⟩ : Circuit).wires y).length = x.length + g.length := by rw [wires_length, hl]
    unfold val at hw ⊢
    rw [wires_snoc] at hw ⊢
    by_cases hlt : w < x.length + g.length
    · rw [List.getD_append _ _ _ _ (by omega)] at hw ⊢
      exact ih' w hw
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hw ⊢
      rw [lx] at hw
      rw [ly]
      cases hk : w - (x.length + g.length) with
      | succ k => rw [hk] at hw; simp at hw
      | zero =>
        rw [hk] at hw
        simp only [List.getD_cons_zero] at hw ⊢
        rcases hg h (by simp) with hop | hop
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hw ⊢
          rintro b ⟨i, hi, rfl⟩
          exact ih' i (hw _ ⟨i, hi, rfl⟩)
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hw ⊢
          obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hw
          exact ⟨_, ⟨i, hi, rfl⟩, ih' i hb⟩

lemma reads_of_ok' {n : ℕ} {g : List Gate} (h : Ok n g) (o : ℕ) : ReadsBack n ⟨g, o⟩ := by
  intro j hj i hi
  have e : gateAt ⟨g, o⟩ j = g[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [e] at hi
  exact h.2 j hj i hi

open Finset

lemma identity (t : ℕ) (ht : 3 ≤ t) :
    2 * (∑ j ∈ (range t).filter (fun j => 1 ≤ j ∧ 2 * j + 1 < t), t.choose j) +
      (if t % 2 = 1 then t.choose (t / 2) else 0) + t.choose (t / 2) + 2 = 2 ^ t := by
  have first : ∀ K, 1 ≤ K → ∑ j ∈ range K, t.choose j = 1 + ∑ j ∈ Ico 1 K, t.choose j := by
    intro K hK
    rw [← sum_range_add_sum_Ico _ hK]
    simp [sum_range_succ]
  have total : ∑ j ∈ range (t + 1), t.choose j = 2 ^ t := Nat.sum_range_choose t
  rcases Nat.even_or_odd' t with ⟨k, hk | hk⟩
  · have hk2 : 1 ≤ k := by omega
    have e : (range t).filter (fun j => 1 ≤ j ∧ 2 * j + 1 < t) = Ico 1 k := by
      ext j
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    have half : t / 2 = k := by omega
    have split : ∑ j ∈ range (t + 1), t.choose j = 2 * (∑ j ∈ range k, t.choose j) + t.choose k := by
      have a : t + 1 = (k + 1) + k := by omega
      rw [a, sum_range_add, sum_range_succ]
      have refl : ∑ x ∈ range k, t.choose (k + 1 + x) = ∑ j ∈ range k, t.choose j := by
        rw [← sum_range_reflect (fun j => t.choose j) k]
        refine sum_congr rfl (fun x hx => ?_)
        have := mem_range.1 hx
        rw [← Nat.choose_symm (by omega : k + 1 + x ≤ t)]
        congr 1
        omega
      rw [refl]
      ring
    rw [e, half, if_neg (by omega)]
    have f := first k hk2
    omega
  · have hk2 : 1 ≤ k := by omega
    have e : (range t).filter (fun j => 1 ≤ j ∧ 2 * j + 1 < t) = Ico 1 k := by
      ext j
      simp only [mem_filter, mem_range, mem_Ico]
      omega
    have half : t / 2 = k := by omega
    have split : ∑ j ∈ range (t + 1), t.choose j = 2 * (∑ j ∈ range k, t.choose j) + 2 * t.choose k := by
      have a : t + 1 = (k + 1) + (k + 1) := by omega
      rw [a, sum_range_add, sum_range_succ]
      have refl : ∑ x ∈ range (k + 1), t.choose (k + 1 + x) = ∑ j ∈ range (k + 1), t.choose j := by
        rw [← sum_range_reflect (fun j => t.choose j) (k + 1)]
        refine sum_congr rfl (fun x hx => ?_)
        have := mem_range.1 hx
        rw [← Nat.choose_symm (by omega : k + 1 + x ≤ t)]
        congr 1
        omega
      rw [refl, sum_range_succ]
      ring
    rw [e, half, if_pos (by omega)]
    have f := first k hk2
    omega

/-- 2e conjuntos distintos, en parejas disjuntas que no cubren todo, caben fuera de la capa central. -/
lemma pair_count {ι : Type} (E : Finset ι) (t : ℕ) (B G : ι → Finset (Fin t))
    (inj : ∀ a ∈ E, ∀ b ∈ E, (B a = B b → a = b) ∧ (G a = G b → a = b) ∧ B a ≠ G b)
    (ne : ∀ a ∈ E, (B a).Nonempty ∧ (G a).Nonempty) (dis : ∀ a ∈ E, Disjoint (B a) (G a))
    (small : ∀ a ∈ E, (B a).card + (G a).card + 1 ≤ t) (nonempty : E.Nonempty) :
    2 * E.card + t.choose (t / 2) + 2 ≤ 2 ^ t := by
  classical
  have ht : 3 ≤ t := by
    obtain ⟨a, ha⟩ := nonempty
    have h1 := card_pos.2 (ne a ha).1
    have h2 := card_pos.2 (ne a ha).2
    have := small a ha
    omega
  let w : Finset (Fin t) → ℕ := fun S =>
    if 1 ≤ S.card ∧ 2 * S.card + 1 < t then 2 else if 2 * S.card + 1 = t then 1 else 0
  have each : ∀ a ∈ E, 2 ≤ w (B a) + w (G a) := by
    intro a ha
    have h1 := card_pos.2 (ne a ha).1
    have h2 := card_pos.2 (ne a ha).2
    have := small a ha
    simp only [w]
    split_ifs <;> omega
  have disjImg : Disjoint (E.image B) (E.image G) := by
    rw [disjoint_left]
    intro S h1 h2
    obtain ⟨a, ha, e1⟩ := mem_image.1 h1
    obtain ⟨b, hb, e2⟩ := mem_image.1 h2
    exact (inj a ha b hb).2.2 (e1.trans e2.symm)
  have lower : 2 * E.card ≤ ∑ S ∈ E.image B ∪ E.image G, w S := by
    rw [sum_union disjImg, sum_image (fun a ha b hb h => (inj a ha b hb).1 h),
      sum_image (fun a ha b hb h => (inj a ha b hb).2.1 h), ← sum_add_distrib]
    have s := sum_le_sum each
    simpa [mul_comm] using s
  have upper : ∑ S ∈ E.image B ∪ E.image G, w S ≤ ∑ S : Finset (Fin t), w S :=
    sum_le_sum_of_subset (subset_univ _)
  have value : ∑ S : Finset (Fin t), w S =
      2 * (∑ j ∈ (range t).filter (fun j => 1 ≤ j ∧ 2 * j + 1 < t), t.choose j) +
        (if t % 2 = 1 then t.choose (t / 2) else 0) := by
    have grp : ∑ S : Finset (Fin t), w S = ∑ j ∈ range (t + 1), t.choose j *
        (if 1 ≤ j ∧ 2 * j + 1 < t then 2 else if 2 * j + 1 = t then 1 else 0) := by
      rw [← powerset_univ, sum_powerset_apply_card (fun j => if 1 ≤ j ∧ 2 * j + 1 < t then 2 else if 2 * j + 1 = t then 1 else 0)]
      simp
    rw [grp]
    have split : ∀ j ∈ range (t + 1), t.choose j * (if 1 ≤ j ∧ 2 * j + 1 < t then 2 else if 2 * j + 1 = t then 1 else 0) =
        (if 1 ≤ j ∧ 2 * j + 1 < t then 2 * t.choose j else 0) + (if 2 * j + 1 = t then t.choose j else 0) := by
      intro j _
      split_ifs <;> omega
    rw [sum_congr rfl split, sum_add_distrib]
    congr 1
    · rw [← sum_filter, mul_sum]
      refine sum_congr ?_ (fun _ _ => rfl)
      ext j
      simp only [mem_filter, mem_range]
      omega
    · split_ifs with h
      · rw [sum_eq_single (t / 2)]
        · rw [if_pos (by omega)]
        · intro j _ hj
          rw [if_neg (by omega)]
        · intro hn
          exact absurd (mem_range.2 (by omega)) hn
      · exact sum_eq_zero (fun j _ => if_neg (by omega))
  have idn := identity t ht
  omega

/-- Compuertas AND que leen solo entradas. -/
lemma and_wires (x : List Bool) (ps : List (ℕ × ℕ)) (h : ∀ p ∈ ps, p.1 < x.length ∧ p.2 < x.length) :
    (⟨ps.map (fun p => ⟨GateOp.and, [p.1, p.2]⟩), 0⟩ : Circuit).wires x =
      x ++ ps.map (fun p => x.getD p.1 false && x.getD p.2 false) := by
  induction ps using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton ps p ih =>
    have ih' := ih (fun q hq => h q (by simp [hq]))
    obtain ⟨h1, h2⟩ := h p (by simp)
    rw [List.map_append, List.map_cons, List.map_nil, wires_snoc]
    unfold val
    rw [ih', List.map_append, ← List.append_assoc]
    congr 1
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]

lemma wire_of {α : Type} [DecidableEq (α → Bool)] (L : List (α → Bool)) (g : α → Bool) (hg : g ∈ L) (x : α) :
    L.idxOf g < L.length ∧ (L.map (fun h => h x)).getD (L.idxOf g) false = g x := by
  have lt := List.idxOf_lt_length_iff.2 hg
  refine ⟨lt, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem lt]
  simp

lemma lado1 (M U V : Prop) (h : ¬ ((M ∧ ¬U) ↔ (M ∧ ¬V))) : M ∧ ¬ (U ↔ V) := by
  by_cases a : M <;> by_cases b : U <;> by_cases c : V <;> simp [a, b, c] at h ⊢

lemma lado2 (M U V : Prop) (h : ¬ ((U ∧ ¬M) ↔ (V ∧ ¬M))) : ¬M ∧ ¬ (U ↔ V) := by
  by_cases a : M <;> by_cases b : U <;> by_cases c : V <;> simp [a, b, c] at h ⊢

end PEqualNP.Outside.L_meta_53203

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_53203 : ∀ (n : Nat) (E : Finset (Fin n × Fin n)), 2 ≤ n →
  (∀ e ∈ E, e.1 < e.2) →
  (∀ Z : Finset (Fin n), (∀ e ∈ E, e.1 ∈ Z ↔ e.2 ∈ Z) → Z = ∅ ∨ Z = Finset.univ) →
  letI : ∀ Q : Prop, Decidable Q := Classical.propDecidable
  let W := Finset (Fin n)
  let bit := fun (i : Fin n) (x : W) => decide (i ∈ x)
  let neg := fun (i : Fin n) (x : W) => !(bit i x)
  let same := fun (e : Fin n × Fin n) (x : W) => bit e.1 x == bit e.2 x
  let raw : Finset (W → Bool) := {fun _ => false,fun _ => true} ∪ Finset.univ.image bit ∪
    E.image same ∪ E.image (fun e x => !(same e x))
  let need := Finset.univ.image neg ∪ E.image (fun e x => neg e.1 x && neg e.2 x) ∪
    E.image (fun e x => bit e.1 x && neg e.2 x) ∪ E.image (fun e x => neg e.1 x && bit e.2 x)
  let keeps := fun A : Finset W => ∀ (S : W) (p : Nat),
    let L := (raw ∪ S.image neg).toList
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
      C.output < L.length+C.size ∧ C.size ≤ p ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
        ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x) ↔
    S.Nonempty ∧ n+3*E.card-S.card ≤ p
  let robust := fun (d b : Nat) => ∃ k : Nat, k ≤ b ∧ ∃ rows : Fin k → W,
    ∀ erased : Finset (Fin k), erased.card ≤ d → keeps ((Finset.univ \ erased).image rows)
  let adj := fun i j : Fin n => (i,j) ∈ E ∨ (j,i) ∈ E
  let near := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
    e.1 < e.2 ∧ (adj e.1 e.2 ∨ ∃ v, adj e.1 v ∧ adj v e.2))
  ∀ (d b C : Nat) (w : Fin n × Fin n → Nat), robust d b →
    (∀ Z : W, (∑ e ∈ near, if (e.1 ∈ Z ↔ e.2 ∈ Z) then 0 else w e) ≤ C) →
    2*(d+1) ≤ b ∧ 2*(d+1)*(∑ e ∈ near, w e) ≤ (b-2*(d+1))*C := by
  intro n E hn hE hconn W bit neg same raw need keeps robust adj near d b C w hrob hcut
  letI dec : DecidableEq (W → Bool) := fun a b => Classical.propDecidable (a = b)
  have bitT : ∀ i x, bit i x = true ↔ i ∈ x := fun i x => by simp [bit]
  have negT : ∀ i x, neg i x = true ↔ i ∉ x := fun i x => by simp [neg, bit]
  have rawF : (fun _ => false : W → Bool) ∈ raw :=
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_insert_self _ _))))))
  have rawT : (fun _ => true : W → Bool) ∈ raw :=
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))))))
  have rawB : ∀ i, bit i ∈ raw := fun i =>
    Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr
      (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))))
  have hne : E.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    let v0 : Fin n := ⟨0, by omega⟩
    have := hconn {v0} (fun e he => by rw [h] at he; exact absurd he (Finset.notMem_empty e))
    rcases this with h1 | h1
    · exact Finset.singleton_ne_empty _ h1
    · have c1 := congrArg Finset.card h1
      rw [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at c1
      omega
  have universal : ∀ (A : Finset W) (L : List (W → Bool)), (fun _ => false) ∈ L → (fun _ => true) ∈ L →
      (∀ f ∈ need, ∀ x ∈ A, ∀ y ∈ A, (∀ g ∈ L, g x = true → g y = true) → f x = true → f y = true) →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack L.length C ∧
        C.output < L.length+C.size ∧ ∀ f ∈ need, ∃ j < L.length+C.size,
          ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = f x := by
    intro A L hf ht mono
    have f0 := List.idxOf_lt_length_iff.2 hf
    have t0 := List.idxOf_lt_length_iff.2 ht
    let ord := need.equivFin
    let T : Fin need.card → List (List ℕ) := fun k =>
      (A.toList.filter (fun x => decide ((ord.symm k).1 x = true))).map
        (fun x => (List.range L.length).filter (fun i => (L.map (fun g => g x)).getD i false))
    have bnd : ∀ k, ∀ term ∈ T k, ∀ i ∈ term, i < L.length := by
      intro k term hterm i hi
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hterm
      exact List.mem_range.1 (List.mem_filter.1 hi).1
    have ok0 : PEqualNP.Outside.L_meta_53203.Ok L.length [] := ⟨by simp, by simp⟩
    obtain ⟨g, o, ext, ho, hv⟩ := PEqualNP.Outside.L_meta_53203.build_many (n := L.length) _ _ f0 t0 need.card T bnd [] ok0
    have f1 := List.idxOf_lt_length_iff.2 hf
    refine ⟨⟨g, L.idxOf (fun _ => false)⟩, ?_, PEqualNP.Outside.L_meta_53203.reads_of_ok' ext.1 _, ?_, ?_⟩
    · intro h hh
      have := ext.1.1 h hh
      exact ⟨by simpa using this.1, this.2⟩
    · show L.idxOf (fun _ => false) < L.length + g.length
      omega
    · intro f hfn
      refine ⟨o (ord ⟨f, hfn⟩), ho _, fun y hy => ?_⟩
      have len : (L.map (fun g => g y)).length = L.length := List.length_map _
      have e0 := (PEqualNP.Outside.L_meta_53203.wire_of L _ hf y).2
      have e1 := (PEqualNP.Outside.L_meta_53203.wire_of L _ ht y).2
      have key := hv _ len e0 e1 (ord ⟨f, hfn⟩)
      change PEqualNP.Outside.L_meta_53203.val (L.map (fun g => g y)) g (o (ord ⟨f, hfn⟩)) = f y
      rw [key, Bool.eq_iff_iff]
      unfold PEqualNP.Outside.L_meta_53203.dnf
      rw [List.any_eq_true]
      simp only [T, Equiv.symm_apply_apply]
      constructor
      · rintro ⟨term, hterm, hall⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hterm
        obtain ⟨hxA, hfx⟩ := List.mem_filter.1 hx
        refine mono f hfn x (Finset.mem_toList.1 hxA) y hy (fun h hh hx1 => ?_) (of_decide_eq_true hfx)
        have wx := PEqualNP.Outside.L_meta_53203.wire_of L h hh x
        have wy := PEqualNP.Outside.L_meta_53203.wire_of L h hh y
        have := List.all_eq_true.1 hall (L.idxOf h) (List.mem_filter.2 ⟨List.mem_range.2 wx.1, by rw [wx.2]; exact hx1⟩)
        rw [wy.2] at this
        exact this
      · intro hfy
        refine ⟨_, List.mem_map.2 ⟨y, List.mem_filter.2 ⟨Finset.mem_toList.2 hy, decide_eq_true hfy⟩, rfl⟩, ?_⟩
        exact List.all_eq_true.2 (fun i hi => (List.mem_filter.1 hi).2)
  have good : ∀ A : Finset W, keeps A →
      ((∅ : Finset (Fin n)) ∈ A ∧ (Finset.univ : Finset (Fin n)) ∈ A) ∧
      (∀ e ∈ E, ∀ k : Fin 3, ∀ g : W → Bool,
        (g ∈ raw ∨ ∃ e' ∈ E, ∃ k' : Fin 3, (e', k') ≠ (e, k) ∧
          g = ![fun x => neg e'.1 x && neg e'.2 x, fun x => bit e'.1 x && neg e'.2 x, fun x => neg e'.1 x && bit e'.2 x] k') →
        ∃ x ∈ A, (![fun x => neg e.1 x && neg e.2 x, fun x => bit e.1 x && neg e.2 x, fun x => neg e.1 x && bit e.2 x] k) x ≠ g x) := by
    intro A hk
    constructor
    · by_contra hno
      let L := (raw ∪ (∅ : Finset (Fin n)).image neg).toList
      have mem : ∀ g, g ∈ raw → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 (Or.inl h))
      obtain ⟨C0, c1, c2, c3, c4⟩ := universal A L (mem _ rawF) (mem _ rawT) (by
        intro f _ x hx y hy hle hfx
        have hbit : ∀ i : Fin n, i ∈ (x : Finset (Fin n)) → i ∈ (y : Finset (Fin n)) := by
          intro i hi
          exact (bitT i y).1 (hle _ (mem _ (rawB i)) ((bitT i x).2 hi))
        have closed : ∀ e ∈ E, e.1 ∈ (y : Finset (Fin n)) \ x ↔ e.2 ∈ (y : Finset (Fin n)) \ x := by
          intro e he
          have m1 : same e ∈ raw :=
            Finset.mem_union.2 (Or.inl (Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))))
          have m2 : (fun x => !(same e x)) ∈ raw :=
            Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨e, he, rfl⟩))
          have hs : same e x = same e y := by
            have a := hle _ (mem _ m1)
            have b := hle _ (mem _ m2)
            cases h1 : same e x
            · rw [h1] at b
              simp only [Bool.not_false, true_implies, Bool.not_eq_true'] at b
              exact b.symm
            · exact (a h1).symm
          have k : ∀ z : W, same e z = true ↔ (e.1 ∈ (z : Finset (Fin n)) ↔ e.2 ∈ (z : Finset (Fin n))) := by
            intro z
            simp only [same, beq_iff_eq]
            rw [Bool.eq_iff_iff, bitT, bitT]
          have s' : (e.1 ∈ (x : Finset (Fin n)) ↔ e.2 ∈ (x : Finset (Fin n))) ↔
              (e.1 ∈ (y : Finset (Fin n)) ↔ e.2 ∈ (y : Finset (Fin n))) := by
            rw [← k x, ← k y, hs]
          have a := hbit e.1
          have b := hbit e.2
          have m : ∀ i, i ∈ (y : Finset (Fin n)) \ x ↔ i ∈ (y : Finset (Fin n)) ∧ i ∉ (x : Finset (Fin n)) := fun i => Finset.mem_sdiff
          rw [m, m]
          clear k hs
          tauto
        have yx : y = x := by
          rcases hconn _ closed with h | h
          · refine Finset.Subset.antisymm (fun i hi => ?_) (fun i hi => hbit i hi)
            by_contra hix
            have : i ∈ (y : Finset (Fin n)) \ x := Finset.mem_sdiff.2 ⟨hi, hix⟩
            rw [h] at this
            exact Finset.notMem_empty _ this
          · exfalso
            have full : ∀ i : Fin n, i ∈ (y : Finset (Fin n)) \ x := fun i => by rw [h]; exact Finset.mem_univ i
            have x0 : (x : Finset (Fin n)) = ∅ :=
              Finset.eq_empty_of_forall_notMem (fun i => (Finset.mem_sdiff.1 (full i)).2)
            have y1 : (y : Finset (Fin n)) = Finset.univ :=
              Finset.eq_univ_of_forall (fun i => (Finset.mem_sdiff.1 (full i)).1)
            apply hno
            constructor
            · rw [← x0]; exact hx
            · rw [← y1]; exact hy
        rw [yx]; exact hfx)
      have res := (hk ∅ C0.size).1 ⟨C0, c1, c2, c3, le_rfl, c4⟩
      exact Finset.not_nonempty_empty res.1
    · intro e he k g hg
      let atom : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q =>
        ![fun x => neg q.1.1 x && neg q.1.2 x, fun x => bit q.1.1 x && neg q.1.2 x, fun x => neg q.1.1 x && bit q.1.2 x] q.2
      let first : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q => ![neg q.1.1, bit q.1.1, neg q.1.1] q.2
      let second : (Fin n × Fin n) × Fin 3 → (W → Bool) := fun q => ![neg q.1.2, neg q.1.2, bit q.1.2] q.2
      have atomEq : ∀ q x, atom q x = (first q x && second q x) := by
        rintro ⟨e, k⟩ x
        fin_cases k <;> rfl
      let Q := E ×ˢ (Finset.univ : Finset (Fin 3))
      have cardQ : Q.card = 3 * E.card := by simp [Q, mul_comm]
      have noCheap : ∀ q ∈ Q, ∀ g : W → Bool,
          (g ∈ raw ∨ g ∈ Finset.univ.image neg ∨ ∃ q' ∈ Q, q' ≠ q ∧ g = atom q') → ∃ x ∈ A, atom q x ≠ g x := by
        intro q hq g hg
        by_contra hall
        have eqA : ∀ x ∈ A, atom q x = g x := by
          intro x hx
          by_contra h
          exact hall ⟨x, hx, h⟩
        let L := (raw ∪ Finset.univ.image neg).toList
        have mem : ∀ g, g ∈ raw ∨ g ∈ Finset.univ.image neg → g ∈ L := fun g h => Finset.mem_toList.2 (Finset.mem_union.2 h)
        have negL : ∀ i, neg i ∈ L := fun i => mem _ (Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
        have bitL : ∀ i, bit i ∈ L := fun i => mem _ (Or.inl (rawB i))
        have firstL : ∀ q', first q' ∈ L := by
          rintro ⟨e, k⟩
          fin_cases k
          · exact negL _
          · exact bitL _
          · exact negL _
        have secondL : ∀ q', second q' ∈ L := by
          rintro ⟨e, k⟩
          fin_cases k
          · exact negL _
          · exact negL _
          · exact bitL _
        let R := (Q.erase q).toList
        let ps : List (ℕ × ℕ) := R.map (fun q' => (L.idxOf (first q'), L.idxOf (second q')))
        let gates : List PEqualNP.CircuitLowerBounds.Gate := ps.map (fun p => ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [p.1, p.2]⟩)
        let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
        have psb : ∀ p ∈ ps, p.1 < L.length ∧ p.2 < L.length := by
          intro p hp
          obtain ⟨q', -, rfl⟩ := List.mem_map.1 hp
          exact ⟨List.idxOf_lt_length_iff.2 (firstL q'), List.idxOf_lt_length_iff.2 (secondL q')⟩
        have size : C.size = 3 * E.card - 1 := by
          show gates.length = _
          simp only [gates, ps, R, List.length_map, Finset.length_toList]
          rw [Finset.card_erase_of_mem hq, cardQ]
        have epos : 0 < E.card := Finset.card_pos.2 hne
        have Lpos : 0 < L.length := lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_iff.2 (negL q.1.1))
        have wiresC : ∀ x : W, C.wires (L.map (fun g => g x)) =
            L.map (fun g => g x) ++ ps.map (fun p => (L.map (fun g => g x)).getD p.1 false && (L.map (fun g => g x)).getD p.2 false) := by
          intro x
          refine PEqualNP.Outside.L_meta_53203.and_wires _ ps (fun p hp => ?_)
          rw [List.length_map]
          exact psb p hp
        have atomWire : ∀ q' ∈ Q, q' ≠ q → ∃ j < L.length + C.size, ∀ x : W,
            (C.wires (L.map (fun g => g x))).getD j false = atom q' x := by
          intro q' hq' hne'
          have inR : q' ∈ R := Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hne', hq'⟩)
          have m := List.idxOf_lt_length_iff.2 inR
          refine ⟨L.length + R.idxOf q', ?_, fun x => ?_⟩
          · have : C.size = R.length := by show gates.length = _; simp [gates, ps]
            omega
          · rw [wiresC, List.getD_append_right _ _ _ _ (by rw [List.length_map]; omega), List.length_map,
              Nat.add_sub_cancel_left, List.getD_eq_getElem?_getD]
            simp only [ps, List.map_map, List.getElem?_map, List.getElem?_eq_getElem m, List.getElem_idxOf, Option.map_some,
              Option.getD_some, Function.comp]
            rw [(PEqualNP.Outside.L_meta_53203.wire_of L _ (firstL q') x).2,
              (PEqualNP.Outside.L_meta_53203.wire_of L _ (secondL q') x).2, atomEq]
        have inputWire : ∀ h ∈ L, ∃ j < L.length + C.size, ∀ x : W, (C.wires (L.map (fun g => g x))).getD j false = h x := by
          intro h hh
          have w := List.idxOf_lt_length_iff.2 hh
          refine ⟨L.idxOf h, by omega, fun x => ?_⟩
          rw [wiresC, List.getD_append _ _ _ _ (by rw [List.length_map]; exact w)]
          exact (PEqualNP.Outside.L_meta_53203.wire_of L h hh x).2
        have res := (hk Finset.univ (3 * E.card - 1)).1 (by
          refine ⟨C, ?_, ?_, ?_, size.le, ?_⟩
          · intro h hh
            obtain ⟨p, -, rfl⟩ := List.mem_map.1 hh
            exact ⟨by simp, by simp⟩
          · intro j hj i hi
            have hj' : j < gates.length := hj
            have e : PEqualNP.MetaComplexity.NestedCover.gateAt C j = gates[j] := by
              simp [PEqualNP.MetaComplexity.NestedCover.gateAt, C, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
            rw [e] at hi
            have : gates[j] ∈ gates := List.getElem_mem _
            obtain ⟨p, hp, ep⟩ := List.mem_map.1 this
            rw [← ep] at hi
            simp at hi
            have := psb p hp
            change i < L.length + j
            omega
          · show 0 < L.length + C.size
            omega
          · intro f hfn
            have hfn' := hfn
            simp only [need, Finset.mem_union, Finset.mem_image] at hfn'
            have atomCase : ∀ q' ∈ Q, ∃ j < L.length + C.size, ∀ x ∈ A, (C.wires (L.map (fun g => g x))).getD j false = atom q' x := by
              intro q' hq'
              by_cases h : q' = q
              · subst h
                rcases hg with hg | hg | ⟨q2, hq2, hne2, rfl⟩
                · obtain ⟨j, hj, w⟩ := inputWire g (mem _ (Or.inl hg))
                  exact ⟨j, hj, fun x hx => (w x).trans (eqA x hx).symm⟩
                · obtain ⟨j, hj, w⟩ := inputWire g (mem _ (Or.inr hg))
                  exact ⟨j, hj, fun x hx => (w x).trans (eqA x hx).symm⟩
                · obtain ⟨j, hj, w⟩ := atomWire q2 hq2 hne2
                  exact ⟨j, hj, fun x hx => (w x).trans (eqA x hx).symm⟩
              · obtain ⟨j, hj, w⟩ := atomWire q' hq' h
                exact ⟨j, hj, fun x _ => w x⟩
            have inQ : ∀ e ∈ E, ∀ k : Fin 3, (e, k) ∈ Q := fun e he k => Finset.mem_product.2 ⟨he, Finset.mem_univ _⟩
            rcases hfn' with ((⟨i, -, rfl⟩ | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
            · obtain ⟨j, hj, w⟩ := inputWire (neg i) (negL i)
              exact ⟨j, hj, fun x _ => w x⟩
            · exact atomCase (e, 0) (inQ e he 0)
            · exact atomCase (e, 1) (inQ e he 1)
            · exact atomCase (e, 2) (inQ e he 2))
        have := res.2
        rw [Finset.card_univ, Fintype.card_fin] at this
        omega
      have inQ : ∀ e ∈ E, ∀ k : Fin 3, (e, k) ∈ Q := fun e he k => Finset.mem_product.2 ⟨he, Finset.mem_univ _⟩
      refine noCheap (e, k) (inQ e he k) g ?_
      rcases hg with hg | ⟨e', he', k', ne', rfl⟩
      · exact Or.inl hg
      · exact Or.inr (Or.inr ⟨(e', k'), inQ e' he' k', ne', rfl⟩)
  obtain ⟨kk, hkb, rows, hrows⟩ := hrob
  classical
  -- toda propiedad que falte al borrar sus filas aparece al menos d+1 veces
  have many : ∀ P : Finset (Fin kk), (d < P.card → False) → ∀ (Q : Finset (Fin n) → Prop),
      (∀ i, Q (rows i) → i ∈ P) → keeps ((Finset.univ \ P).image rows) ∧ ∀ x ∈ (Finset.univ \ P).image rows, ¬ Q x := by
    intro P hP Q hQ
    refine ⟨by convert hrows P (not_lt.1 hP), fun x hx hq => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
    exact (Finset.mem_sdiff.1 hi).2 (hQ i hq)
  let Z0 : Finset (Fin kk) := Finset.univ.filter (fun i => rows i = (∅ : Finset (Fin n)))
  let Z1 : Finset (Fin kk) := Finset.univ.filter (fun i => rows i = (Finset.univ : Finset (Fin n)))
  have z0 : d < Z0.card := by
    by_contra h
    obtain ⟨hk, no⟩ := many Z0 h (fun x => x = ∅) (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    exact no _ (good _ hk).1.1 rfl
  have z1 : d < Z1.card := by
    by_contra h
    obtain ⟨hk, no⟩ := many Z1 h (fun x => x = Finset.univ) (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    exact no _ (good _ hk).1.2 rfl
  have d01 : Disjoint Z0 Z1 := by
    rw [Finset.disjoint_left]
    intro i h0 h1
    have a := (Finset.mem_filter.1 h0).2
    have b := (Finset.mem_filter.1 h1).2
    rw [a] at b
    have c1 := congrArg Finset.card b
    rw [Finset.card_empty, Finset.card_univ, Fintype.card_fin] at c1
    omega
  have two : 2 * (d + 1) ≤ Z0.card + Z1.card := by omega
  have le_k : Z0.card + Z1.card ≤ kk := by
    rw [← Finset.card_union_of_disjoint d01]
    simpa using Finset.card_le_univ (Z0 ∪ Z1)
  refine ⟨by omega, ?_⟩
  let Sep : Fin n × Fin n → Finset (Fin kk) := fun p =>
    Finset.univ.filter (fun i => ¬ (p.1 ∈ rows i ↔ p.2 ∈ rows i))
  let atom : (Fin n × Fin n) → Fin 3 → (W → Bool) := fun e k =>
    ![fun x => neg e.1 x && neg e.2 x, fun x => bit e.1 x && neg e.2 x, fun x => neg e.1 x && bit e.2 x] k
  have a1 : ∀ e (x : W), atom e 1 x = true ↔ e.1 ∈ (x : Finset (Fin n)) ∧ e.2 ∉ (x : Finset (Fin n)) := fun e x => by
    show (bit e.1 x && neg e.2 x) = true ↔ _
    rw [Bool.and_eq_true, bitT, negT]
  have a2 : ∀ e (x : W), atom e 2 x = true ↔ e.1 ∉ (x : Finset (Fin n)) ∧ e.2 ∈ (x : Finset (Fin n)) := fun e x => by
    show (neg e.1 x && bit e.2 x) = true ↔ _
    rw [Bool.and_eq_true, negT, bitT]
  have halves : ∀ (p : Fin n × Fin n) (T1 T2 : Finset (Fin kk)), d < T1.card → d < T2.card →
      (∀ i ∈ T1, i ∉ T2) → (∀ i, i ∈ T1 ∨ i ∈ T2 → ¬ (p.1 ∈ rows i ↔ p.2 ∈ rows i)) → 2 * (d + 1) ≤ (Sep p).card := by
    intro p T1 T2 h1 h2 excl sep
    have sub : ∀ i, i ∈ T1 ∨ i ∈ T2 → i ∈ Sep p := fun i hi => by
      simp only [Sep, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, sep i hi⟩
    let U := T1.disjUnion T2 (Finset.disjoint_left.2 (fun i => excl i))
    have c : U.card ≤ (Sep p).card := Finset.card_le_card (fun i hi => sub i (Finset.mem_disjUnion.1 hi))
    rw [Finset.card_disjUnion] at c
    omega
  have separated : ∀ p ∈ near, 2 * (d + 1) ≤ (Sep p).card := by
    intro p hp
    have hp' : p.1 < p.2 ∧ (adj p.1 p.2 ∨ ∃ v, adj p.1 v ∧ adj v p.2) := by
      have := hp
      simp only [near, Finset.mem_filter] at this
      exact this.2
    obtain ⟨lt, h | ⟨m, h1, h2⟩⟩ := hp'
    · have pE : p ∈ E := by
        rcases h with h | h
        · exact h
        · exact absurd (hE _ h) (not_lt.2 lt.le)
      have one : ∀ k : Fin 3, d < (Finset.univ.filter (fun i => atom p k (rows i) = true)).card := by
        intro k
        by_contra hc
        obtain ⟨hk, no⟩ := many _ hc (fun x => atom p k x = true) (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        obtain ⟨x, hx, ne⟩ := (good _ hk).2 p pE k (fun _ => false) (Or.inl rawF)
        apply ne
        show atom p k x = false
        rw [← Bool.not_eq_true]
        exact no x hx
      refine halves p _ _ (one 1) (one 2) (fun i u v => ?_) (fun i h => ?_)
      · simp only [Finset.mem_filter] at u v
        have x := (a1 p _).1 u.2
        have y := (a2 p _).1 v.2
        exact y.1 x.1
      · simp only [Finset.mem_filter] at h
        rcases h with h | h
        · have x := (a1 p _).1 h.2
          exact fun e => x.2 (e.1 x.1)
        · have x := (a2 p _).1 h.2
          exact fun e => x.1 (e.2 x.2)
    · have loop : ∀ i j, adj i j → i ≠ j := by
        intro i j h e
        subst e
        rcases h with h | h <;> exact lt_irrefl _ (hE _ h)
      -- cada lado del camino es una arista ordenada, con la orientacion que corresponde
      have edge : ∀ u, adj u m → ∃ e ∈ E, (e.1 = m ∨ e.2 = m) ∧ (e.1 = u ∨ e.2 = u) ∧
          (∃ k : Fin 3, ∀ x : W, atom e k x = true ↔ m ∈ (x : Finset (Fin n)) ∧ u ∉ (x : Finset (Fin n))) ∧
          (∃ k : Fin 3, ∀ x : W, atom e k x = true ↔ u ∈ (x : Finset (Fin n)) ∧ m ∉ (x : Finset (Fin n))) := by
        intro u h
        rcases h with h | h
        · refine ⟨(u, m), h, Or.inr rfl, Or.inl rfl, ⟨2, fun x => ?_⟩, ⟨1, fun x => a1 (u, m) x⟩⟩
          rw [a2]; exact and_comm
        · refine ⟨(m, u), h, Or.inl rfl, Or.inr rfl, ⟨1, fun x => a1 (m, u) x⟩, ⟨2, fun x => ?_⟩⟩
          rw [a2]; exact and_comm
      have h2' : adj p.2 m := h2.symm
      obtain ⟨e, eE, em, eu, ⟨k1, ek1⟩, ⟨k2, ek2⟩⟩ := edge p.1 h1
      obtain ⟨f, fE, fm, fv, ⟨l1, fl1⟩, ⟨l2, fl2⟩⟩ := edge p.2 h2'
      have ef : e ≠ f := by
        intro h
        subst h
        have n1 : p.1 ≠ m := loop _ _ h1
        have n2 : p.2 ≠ m := loop _ _ h2'
        have n3 : p.1 ≠ p.2 := ne_of_lt lt
        rcases em with em | em <;> rcases eu with eu | eu <;> rcases fv with fv | fv
        all_goals first
          | exact n3 (eu.symm.trans fv)
          | exact n1 (eu.symm.trans em)
          | exact n2 (fv.symm.trans em)
      have part : ∀ (k l : Fin 3) (R : Finset (Fin n) → Prop), (∀ x : W, atom e k x ≠ atom f l x → R x) →
          ∀ [DecidablePred fun i => R (rows i)], d < (Finset.univ.filter (fun i => R (rows i))).card := by
        intro k l R back _
        by_contra hc
        obtain ⟨hk, no⟩ := many _ hc R (fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        obtain ⟨x, hx, ne⟩ := (good _ hk).2 e eE k (atom f l)
          (Or.inr ⟨f, fE, l, fun h => ef (Prod.mk.inj h).1.symm, rfl⟩)
        exact no x hx (back x ne)
      have diff : ∀ (s t : Bool) (P Q : Prop), (s = true ↔ P) → (t = true ↔ Q) → s ≠ t → ¬ (P ↔ Q) := by
        intro s t P Q hs ht h
        rwa [← hs, ← ht, ← Bool.eq_iff_iff]
      have q1 : d < (Finset.univ.filter (fun i => m ∈ rows i ∧ ¬ (p.1 ∈ rows i ↔ p.2 ∈ rows i))).card :=
        part k1 l1 (fun x => m ∈ x ∧ ¬ (p.1 ∈ x ↔ p.2 ∈ x))
          (fun x h => PEqualNP.Outside.L_meta_53203.lado1 _ _ _ (diff _ _ _ _ (ek1 x) (fl1 x) h))
      have q2 : d < (Finset.univ.filter (fun i => m ∉ rows i ∧ ¬ (p.1 ∈ rows i ↔ p.2 ∈ rows i))).card :=
        part k2 l2 (fun x => m ∉ x ∧ ¬ (p.1 ∈ x ↔ p.2 ∈ x))
          (fun x h => PEqualNP.Outside.L_meta_53203.lado2 _ _ _ (diff _ _ _ _ (ek2 x) (fl2 x) h))
      refine halves p _ _ q1 q2 (fun i u v => ?_) (fun i h => ?_)
      · simp only [Finset.mem_filter] at u v
        exact v.2.1 u.2.1
      · simp only [Finset.mem_filter] at h
        rcases h with h | h <;> exact h.2.2
  -- doble conteo
  let val : Fin kk → ℕ := fun i => ∑ e ∈ near, if (e.1 ∈ rows i ↔ e.2 ∈ rows i) then 0 else w e
  have swap : ∑ i, val i = ∑ e ∈ near, (Sep e).card * w e := by
    simp only [val]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [Sep]
    rw [Finset.card_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : (e.1 ∈ rows i ↔ e.2 ∈ rows i)
    · rw [if_pos h, if_neg (not_not.2 h), Nat.zero_mul]
    · rw [if_neg h, if_pos h, Nat.one_mul]
  have low : 2 * (d + 1) * (∑ e ∈ near, w e) ≤ ∑ i, val i := by
    rw [swap, Finset.mul_sum]
    exact Finset.sum_le_sum (fun e he => Nat.mul_le_mul_right _ (separated e he))
  have zero : ∀ i ∈ Z0 ∪ Z1, val i = 0 := by
    intro i hi
    refine Finset.sum_eq_zero (fun e _ => ?_)
    refine if_pos ?_
    rcases Finset.mem_union.1 hi with h | h
    · rw [(Finset.mem_filter.1 h).2]
      exact iff_of_false (Finset.notMem_empty _) (Finset.notMem_empty _)
    · rw [(Finset.mem_filter.1 h).2]
      exact iff_of_true (Finset.mem_univ _) (Finset.mem_univ _)
  have high : ∑ i, val i ≤ (kk - (Z0.card + Z1.card)) * C := by
    have s := Finset.sum_sdiff (f := val) (Finset.subset_univ (Z0 ∪ Z1))
    rw [Finset.sum_eq_zero zero, Nat.add_zero] at s
    rw [← s]
    have c : (Finset.univ \ (Z0 ∪ Z1)).card = kk - (Z0.card + Z1.card) := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        Finset.card_union_of_disjoint d01]
    rw [← c]
    have := Finset.sum_le_card_nsmul (Finset.univ \ (Z0 ∪ Z1)) val C (fun i _ => by
      have h := hcut (rows i)
      exact le_trans (le_of_eq (by
        refine Finset.sum_congr rfl (fun e _ => ?_)
        congr)) h)
    simpa using this
  exact low.trans (high.trans (Nat.mul_le_mul_right _ (by omega)))
