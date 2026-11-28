import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53186

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

def bits {n : ℕ} (s : Finset (Fin n)) : List Bool := List.ofFn (fun j => decide (j ∈ s))

lemma bits_length {n : ℕ} (s : Finset (Fin n)) : (bits s).length = n := by simp [bits]

lemma bits_get {n : ℕ} (s : Finset (Fin n)) (w : ℕ) : (bits s).getD w false = true ↔ ∃ h : w < n, (⟨w, h⟩ : Fin n) ∈ s := by
  by_cases h : w < n
  · simp [bits, List.getD_eq_getElem?_getD, h]
  · simp [bits, List.getD_eq_getElem?_getD, h]

lemma app_mono (a a' c : List Bool) (hl : a.length = a'.length) (h : ∀ w, a.getD w false = true → a'.getD w false = true) :
    ∀ w, (a ++ c).getD w false = true → (a' ++ c).getD w false = true := by
  intro w hw
  by_cases hlt : w < a.length
  · rw [List.getD_append _ _ _ _ hlt] at hw
    rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
    exact h w hw
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hw
    rw [List.getD_append_right _ _ _ _ (by omega), ← hl]
    exact hw

lemma bits_mono {n : ℕ} {s t : Finset (Fin n)} (h : s ⊆ t) : ∀ w, (bits s).getD w false = true → (bits t).getD w false = true := by
  intro w hw
  obtain ⟨hn, hm⟩ := (bits_get s w).1 hw
  exact (bits_get t w).2 ⟨hn, h hm⟩

lemma reads_of_ok {n : ℕ} {g : List Gate} (h : Ok n g) : ReadsBack n ⟨g, 0⟩ := by
  intro j hj i hi
  have e : gateAt ⟨g, 0⟩ j = g[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [e] at hi
  exact h.2 j hj i hi

def Crit {m d a : ℕ} (X : Fin m → Finset (Fin d)) (Y : Fin m → Finset (Fin a)) (i j : Fin m) : Prop :=
  X i ⊆ X j ∧ ¬ Y i ⊆ Y j

lemma terms_fold (g : List Bool) (base : List ℕ) {τ σ : Type} (ts : List τ) (Ls : List σ) (f : τ → σ → List ℕ) :
    (∃ term ∈ ts.foldr (fun t acc => Ls.flatMap (fun L => acc.map (fun s => f t L ++ s))) [base],
        term.all (fun w => g.getD w false) = true) ↔
      (∀ t ∈ ts, ∃ L ∈ Ls, (f t L).all (fun w => g.getD w false) = true) ∧ base.all (fun w => g.getD w false) = true := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldr_cons, List.forall_mem_cons]
    constructor
    · rintro ⟨term, hm, hall⟩
      obtain ⟨L, hL, hm⟩ := List.mem_flatMap.1 hm
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
      rw [List.all_append, Bool.and_eq_true] at hall
      have := ih.1 ⟨s, hs, hall.2⟩
      exact ⟨⟨⟨L, hL, hall.1⟩, this.1⟩, this.2⟩
    · rintro ⟨⟨⟨L, hL, h1⟩, h2⟩, h3⟩
      obtain ⟨s, hs, h4⟩ := ih.2 ⟨h2, h3⟩
      refine ⟨f t L ++ s, List.mem_flatMap.2 ⟨L, hL, List.mem_map.2 ⟨s, hs, rfl⟩⟩, ?_⟩
      rw [List.all_append, Bool.and_eq_true]
      exact ⟨h1, h4⟩

lemma fold_bound (n : ℕ) (base : List ℕ) {τ σ : Type} (ts : List τ) (Ls : List σ) (f : τ → σ → List ℕ)
    (hb : ∀ w ∈ base, w < n) (hf : ∀ t L, ∀ w ∈ f t L, w < n) :
    ∀ term ∈ ts.foldr (fun t acc => Ls.flatMap (fun L => acc.map (fun s => f t L ++ s))) [base], ∀ w ∈ term, w < n := by
  induction ts with
  | nil => simpa using hb
  | cons t ts ih =>
    intro term hm w hw
    obtain ⟨L, -, hm⟩ := List.mem_flatMap.1 hm
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
    rcases List.mem_append.1 hw with hw | hw
    · exact hf t L w hw
    · exact ih s hs w hw

theorem main (m d a b : ℕ) (X : Fin m → Finset (Fin d)) (Y : Fin m → Finset (Fin a))
  (D U : Finset (Finset (Fin b))) (hD : ∅ ∈ D) (hU : ∅ ∈ U) :
  (∃ (P Q : Circuit) (s : Fin b → ℕ) (o : Fin a → ℕ),
    let high := fun i => (Finset.univ : Finset (Fin b)).filter (fun j =>
      (P.wires (bits (X i) ++ [false,true])).getD (s j) false = false)
    Monotone2 P ∧ Monotone2 Q ∧
    ReadsBack (d+2) P ∧
    ReadsBack (d+b+2) Q ∧
    (∀ j, s j < d+2+P.size) ∧ (∀ j, o j < d+b+2+Q.size) ∧
    ∀ i (z : Finset (Fin b)), (∃ L ∈ D, high i \ z ⊆ L) → (∃ R ∈ U, z \ high i ⊆ R) →
      ∀ j, (Q.wires (bits (X i) ++ bits z ++ [false,true])).getD (o j) false = decide (j ∈ Y i)) ↔
  ∃ (k : ℕ) (B : Fin k → Finset (Fin b)),
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, ∀ L ∈ D, ∀ R ∈ U, ¬ B i ⊆ L ∪ R) ∧
    ¬ ∃ lo hi : Fin (k+1) → Fin m,
      (∀ t, X (lo t) ⊆ X (hi t) ∧ ¬ Y (lo t) ⊆ Y (hi t)) ∧
      (∀ t u, t < u → X (hi t) ⊆ X (lo u)) := by
  constructor
  · rintro ⟨P, Q, s, o, hP⟩
    obtain ⟨mP, mQ, -, -, -, -, hrun⟩ := hP
    let high : Fin m → Finset (Fin b) := fun i => (Finset.univ : Finset (Fin b)).filter (fun j =>
      (P.wires (bits (X i) ++ [false,true])).getD (s j) false = false)
    have anti : ∀ i j, X i ⊆ X j → high j ⊆ high i := by
      intro i j hX k hk
      simp only [high, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_contra hne
      have h1 : val (bits (X i) ++ [false,true]) P.gates (s k) = true := by
        simpa [val, Circuit.wires] using hne
      have h2 := circuit_mono P.gates (fun g hg => by simpa using (mP g hg).1) _ (bits (X j) ++ [false,true])
        (by simp [bits_length]) (app_mono _ _ _ (by simp [bits_length]) (bits_mono hX)) _ h1
      have h3 : (P.wires (bits (X j) ++ [false,true])).getD (s k) false = true := h2
      rw [hk] at h3
      exact Bool.false_ne_true h3
    have escape : ∀ i j, X i ⊆ X j → ¬ Y i ⊆ Y j → ∀ L ∈ D, ∀ R ∈ U, ¬ high i \ high j ⊆ L ∪ R := by
      intro i j hX hY L hL R hR hS
      let zi := high i \ ((high i \ high j) ∩ L)
      let zj := high j ∪ ((high i \ high j) \ L)
      have v1 : high i \ zi ⊆ L := by
        intro e he
        simp only [zi, Finset.mem_sdiff, not_and, not_not] at he
        exact (Finset.mem_inter.1 (he.2 he.1)).2
      have v2 : zi \ high i ⊆ ∅ := by
        have : zi \ high i = ∅ := Finset.sdiff_eq_empty_iff_subset.2 Finset.sdiff_subset
        rw [this]
      have v3 : high j \ zj ⊆ ∅ := by
        have : high j \ zj = ∅ := Finset.sdiff_eq_empty_iff_subset.2 Finset.subset_union_left
        rw [this]
      have v4 : zj \ high j ⊆ R := by
        intro e he
        obtain ⟨h1, hn⟩ := Finset.mem_sdiff.1 he
        rcases Finset.mem_union.1 h1 with h | h
        · exact absurd h hn
        · obtain ⟨hs, hnl⟩ := Finset.mem_sdiff.1 h
          rcases Finset.mem_union.1 (hS hs) with h' | h'
          · exact absurd h' hnl
          · exact h'
      have hz : zi ⊆ zj := by
        intro e he
        obtain ⟨hei, hne⟩ := Finset.mem_sdiff.1 he
        by_cases hj : e ∈ high j
        · exact Finset.mem_union_left _ hj
        · refine Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨hei, hj⟩, fun hl => ?_⟩)
          exact hne (Finset.mem_inter.2 ⟨Finset.mem_sdiff.2 ⟨hei, hj⟩, hl⟩)
      obtain ⟨t, hti, htj⟩ := Finset.not_subset.1 hY
      have r1 : (Q.wires (bits (X i) ++ bits zi ++ [false,true])).getD (o t) false = true := by
        rw [hrun i zi ⟨L, hL, by convert v1⟩ ⟨∅, hU, by convert v2⟩ t]; simp [hti]
      have r2 : (Q.wires (bits (X j) ++ bits zj ++ [false,true])).getD (o t) false = false := by
        rw [hrun j zj ⟨∅, hD, by convert v3⟩ ⟨R, hR, by convert v4⟩ t]; simp [htj]
      have h2 := circuit_mono Q.gates (fun g hg => by simpa using (mQ g hg).1)
        (bits (X i) ++ bits zi ++ [false,true]) (bits (X j) ++ bits zj ++ [false,true]) (by simp [bits_length])
        (by
          apply app_mono _ _ _ (by simp [bits_length])
          intro w hw
          by_cases hlt : w < d
          · rw [List.getD_append _ _ _ _ (by rw [bits_length]; exact hlt)] at hw ⊢
            exact bits_mono hX w hw
          · rw [List.getD_append_right _ _ _ _ (by rw [bits_length]; omega)] at hw
            rw [List.getD_append_right _ _ _ _ (by rw [bits_length]; omega)]
            rw [bits_length] at hw ⊢
            exact bits_mono hz _ hw)
        (o t) r1
      have h3 : (Q.wires (bits (X j) ++ bits zj ++ [false,true])).getD (o t) false = true := h2
      rw [r2] at h3
      exact Bool.false_ne_true h3
    let Has : ℕ → Prop := fun K => ∃ lo hi : Fin K → Fin m,
      (∀ t, X (lo t) ⊆ X (hi t) ∧ ¬ Y (lo t) ⊆ Y (hi t)) ∧ (∀ t u, t < u → X (hi t) ⊆ X (lo u))
    have disj : ∀ (K : ℕ) (lo hi : Fin K → Fin m), (∀ t u, t < u → X (hi t) ⊆ X (lo u)) →
        ∀ t u, t ≠ u → Disjoint (high (lo t) \ high (hi t)) (high (lo u) \ high (hi u)) := by
      intro K lo hi hc
      have lt : ∀ t u, t < u → Disjoint (high (lo t) \ high (hi t)) (high (lo u) \ high (hi u)) := by
        intro t u htu
        rw [Finset.disjoint_left]
        intro e he hu
        exact (Finset.mem_sdiff.1 he).2 (anti _ _ (hc t u htu) (Finset.mem_sdiff.1 hu).1)
      intro t u hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact lt t u h
      · exact (lt u t h).symm
    have bound : ∀ K, Has K → K ≤ b := by
      rintro K ⟨lo, hi, h1, h2⟩
      have ne : ∀ t, ∃ e, e ∈ high (lo t) \ high (hi t) := by
        intro t
        have : ¬ high (lo t) \ high (hi t) ⊆ ∅ ∪ ∅ := escape _ _ (h1 t).1 (h1 t).2 ∅ hD ∅ hU
        obtain ⟨e, he, -⟩ := Finset.not_subset.1 this
        exact ⟨e, he⟩
      choose e he using ne
      have inj : Function.Injective e := by
        intro t u h
        by_contra hne
        exact Finset.disjoint_left.1 (disj K lo hi h2 t u hne) (he t) (h ▸ he u)
      simpa using Fintype.card_le_of_injective e inj
    have has0 : Has 0 := ⟨fun t => t.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0⟩
    have : DecidablePred Has := Classical.decPred _
    have hk : Has (Nat.findGreatest Has b) := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) has0
    obtain ⟨lo, hi, h1, h2⟩ := hk
    refine ⟨Nat.findGreatest Has b, fun t => high (lo t) \ high (hi t), ?_, ?_, ?_⟩
    · intro t u h
      exact disj _ lo hi h2 t u h
    · intro t L hL R hR h
      exact escape _ _ (h1 t).1 (h1 t).2 L hL R hR h
    · intro h
      have h' : Has (Nat.findGreatest Has b + 1) := h
      exact Nat.findGreatest_is_greatest (P := Has) (Nat.lt_succ_self _) (bound _ h') h'
  · rintro ⟨k, B, hdis, hesc, hno⟩
    let Below : Finset (Fin d) → ℕ → Prop := fun x K =>
      ∃ lo hi : Fin K → Fin m, (∀ t, X (lo t) ⊆ X (hi t) ∧ ¬ Y (lo t) ⊆ Y (hi t)) ∧
        (∀ t u, t < u → X (hi t) ⊆ X (lo u)) ∧ ∀ t, X (hi t) ⊆ x
    have : ∀ x, DecidablePred (Below x) := fun x => Classical.decPred _
    let g : Finset (Fin d) → ℕ := fun x => Nat.findGreatest (Below x) k
    have below0 : ∀ x, Below x 0 := fun x =>
      ⟨fun t => t.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0⟩
    have gspec : ∀ x, Below x (g x) := fun x => Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (below0 x)
    have gle : ∀ x, g x ≤ k := fun x => Nat.findGreatest_le _
    have gmono : ∀ x y, x ⊆ y → g x ≤ g y := by
      intro x y h
      obtain ⟨lo, hi, h1, h2, h3⟩ := gspec x
      exact Nat.le_findGreatest (gle x) ⟨lo, hi, h1, h2, fun t => (h3 t).trans h⟩
    have step : ∀ i j, X i ⊆ X j → ¬ Y i ⊆ Y j → g (X i) + 1 ≤ g (X j) := by
      intro i j hX hY
      obtain ⟨lo, hi, h1, h2, h3⟩ := gspec (X i)
      have ext : Below (X j) (g (X i) + 1) := by
        refine ⟨Fin.snoc lo i, Fin.snoc hi j, ?_, ?_, ?_⟩
        · intro t
          refine Fin.lastCases ?_ (fun t => ?_) t
          · simp only [Fin.snoc_last]; exact ⟨hX, hY⟩
          · simp only [Fin.snoc_castSucc]; exact h1 t
        · intro t u htu
          revert htu
          refine Fin.lastCases ?_ (fun t => ?_) t
          · intro h; exact absurd h (not_lt.2 (Fin.le_last u))
          · refine Fin.lastCases ?_ (fun u => ?_) u
            · intro _; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact h3 t
            · intro h; simp only [Fin.snoc_castSucc]; exact h2 t u (by simpa using h)
        · intro t
          refine Fin.lastCases ?_ (fun t => ?_) t
          · simp only [Fin.snoc_last]; exact Finset.Subset.refl _
          · simp only [Fin.snoc_castSucc]; exact (h3 t).trans hX
      have : g (X i) + 1 ≤ k := by
        by_contra hlt
        have e : g (X i) + 1 = k + 1 := by have := gle (X i); omega
        rw [e] at ext
        obtain ⟨lo', hi', h1', h2', -⟩ := ext
        exact hno ⟨lo', hi', h1', h2'⟩
      exact Nat.le_findGreatest this ext
    have : ∀ w : Fin b, Decidable (∃ t, w ∈ B t) := fun w => Classical.propDecidable _
    let tx : Fin m → List ℕ := fun i => (X i).toList.map Fin.val
    let TP : Fin b → List (List ℕ) := fun w => if h : ∃ t, w ∈ B t then
      ((List.finRange m).filter (fun i => decide ((Classical.choose h).val < g (X i)))).map tx else [[]]
    let ts : Fin m → List (Fin k) := fun i => (List.finRange k).filter (fun t => decide (g (X i) ≤ t.val))
    let part : Fin k → Finset (Fin b) → List ℕ := fun t L => (B t \ L).toList.map (fun e => d + e.val)
    let Ti : Fin m → List (List ℕ) := fun i =>
      (ts i).foldr (fun t acc => D.toList.flatMap (fun L => acc.map (fun s => part t L ++ s))) [tx i]
    let TQ : Fin a → List (List ℕ) := fun j => ((List.finRange m).filter (fun i => decide (j ∈ Y i))).flatMap Ti
    have ok0 : ∀ n, Ok n [] := fun n => ⟨by simp, by simp⟩
    have htx : ∀ i, ∀ w ∈ tx i, w < d := by
      intro i w hw
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hw
      exact e.isLt
    obtain ⟨gp, s, eP, hs, hvP⟩ := build_many (n := d+2) d (d+1) (by omega) (by omega) b TP (by
      intro w term hterm x hx
      by_cases h : ∃ t, w ∈ B t
      · simp only [TP, dif_pos h] at hterm
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hterm
        have := htx i x hx
        omega
      · simp only [TP, dif_neg h, List.mem_singleton] at hterm
        subst hterm
        simp at hx) [] (ok0 _)
    obtain ⟨gq, o, eQ, ho, hvQ⟩ := build_many (n := d+b+2) (d+b) (d+b+1) (by omega) (by omega) a TQ (by
      intro j term hterm w hw
      obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hterm
      refine fold_bound (d+b+2) (tx i) (ts i) D.toList part ?_ ?_ term hi w hw
      · intro v hv
        have := htx i v hv; omega
      · intro t L v hv
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hv
        have := e.isLt; omega) [] (ok0 _)
    have inX : ∀ (n : Fin m) (c : List Bool) (i : Fin m),
        ((tx i).all (fun w => (bits (X n) ++ c).getD w false) = true ↔ X i ⊆ X n) := by
      intro n c i
      simp only [tx, List.all_eq_true, List.mem_map, Finset.mem_toList]
      constructor
      · intro H' e he
        have := H' e.val ⟨e, he, rfl⟩
        rw [List.getD_append _ _ _ _ (by rw [bits_length]; exact e.isLt)] at this
        obtain ⟨_, hm⟩ := (bits_get _ _).1 this
        exact hm
      · rintro H' w ⟨e, he, rfl⟩
        rw [List.getD_append _ _ _ _ (by rw [bits_length]; exact e.isLt)]
        exact (bits_get _ _).2 ⟨e.isLt, H' he⟩
    have wireP : ∀ n w, val (bits (X n) ++ [false,true]) gp (s w) = true ↔ ∀ t, w ∈ B t → t.val < g (X n) := by
      intro n w
      rw [hvP _ (by simp [bits_length]) (by rw [List.getD_append_right _ _ _ _ (by rw [bits_length]), bits_length]; simp)
        (by rw [List.getD_append_right _ _ _ _ (by rw [bits_length]; omega), bits_length]; simp) w]
      unfold dnf
      rw [List.any_eq_true]
      by_cases h : ∃ t, w ∈ B t
      · have hc := Classical.choose_spec h
        have uniq : ∀ t, w ∈ B t → t = Classical.choose h := by
          intro t ht
          by_contra hne
          exact Finset.disjoint_left.1 (hdis _ _ hne) ht hc
        simp only [TP, dif_pos h]
        constructor
        · rintro ⟨term, hterm, hall⟩ t ht
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hterm
          have h1 := of_decide_eq_true (List.mem_filter.1 hi).2
          rw [uniq t ht]
          exact lt_of_lt_of_le h1 (gmono _ _ ((inX n _ i).1 hall))
        · intro hall
          exact ⟨tx n, List.mem_map.2 ⟨n, List.mem_filter.2 ⟨List.mem_finRange _, decide_eq_true (hall _ hc)⟩, rfl⟩,
            (inX n _ n).2 (Finset.Subset.refl _)⟩
      · simp only [TP, dif_neg h]
        constructor
        · intro _ t ht
          exact absurd ⟨t, ht⟩ h
        · intro _
          exact ⟨[], by simp, by simp⟩
    refine ⟨⟨gp, 0⟩, ⟨gq, 0⟩, s, o, ?_⟩
    intro high
    have highEq : ∀ i w, w ∈ high i ↔ ∃ t : Fin k, g (X i) ≤ t.val ∧ w ∈ B t := by
      intro i w
      simp only [high, Finset.mem_filter, Finset.mem_univ, true_and]
      have key := wireP i w
      unfold val at key
      rw [← Bool.not_eq_true, key]
      constructor
      · intro h
        by_contra hc
        apply h
        intro t ht
        by_contra hlt
        exact hc ⟨t, not_lt.1 hlt, ht⟩
      · rintro ⟨t, h1, h2⟩ h
        exact absurd (h t h2) (not_lt.2 h1)
    refine ⟨?_, ?_, reads_of_ok eP.1, reads_of_ok eQ.1, hs, ho, ?_⟩
    · intro x hx
      have := eP.1.1 x hx
      exact ⟨by simpa using this.1, this.2⟩
    · intro x hx
      have := eQ.1.1 x hx
      exact ⟨by simpa using this.1, this.2⟩
    rintro n z ⟨L0, hL0, hdown⟩ ⟨R, hR, hup⟩ j
    have hx : (bits (X n) ++ bits z ++ [false,true]).length = d+b+2 := by simp [bits_length]; omega
    have hv := hvQ _ hx
      (by rw [List.getD_append_right _ _ _ _ (by simp [bits_length])]; simp [bits_length])
      (by rw [List.getD_append_right _ _ _ _ (by simp [bits_length])]; simp [bits_length]) j
    change val (bits (X n) ++ bits z ++ [false,true]) gq (o j) = _
    rw [hv, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    have inZ : ∀ W : Finset (Fin b), ((W.toList.map (fun e => d + e.val)).all
        (fun w => (bits (X n) ++ bits z ++ [false,true]).getD w false) = true ↔ ∀ e ∈ W, e ∈ z) := by
      intro W
      have key : ∀ e : Fin b, (bits (X n) ++ bits z ++ [false,true]).getD (d + e.val) false = (bits z).getD e.val false := by
        intro e
        have := e.isLt
        rw [List.getD_append _ _ _ _ (by simp [bits_length] <;> omega),
          List.getD_append_right _ _ _ _ (by rw [bits_length]; omega), bits_length, Nat.add_sub_cancel_left]
      simp only [List.all_eq_true, List.mem_map, Finset.mem_toList]
      constructor
      · intro H' e he
        have := H' _ ⟨e, he, rfl⟩
        rw [key] at this
        obtain ⟨_, hm⟩ := (bits_get _ _).1 this
        exact hm
      · rintro H' w ⟨e, he, rfl⟩
        rw [key]
        exact (bits_get _ _).2 ⟨e.isLt, H' e he⟩
    have inX' : ∀ i, ((tx i).all (fun w => (bits (X n) ++ bits z ++ [false,true]).getD w false) = true ↔ X i ⊆ X n) := by
      intro i
      rw [List.append_assoc]
      exact inX n _ i
    unfold dnf
    rw [List.any_eq_true]
    constructor
    · rintro ⟨term, hterm, hall⟩
      obtain ⟨i, hi, hm⟩ := List.mem_flatMap.1 hterm
      have hjY : j ∈ Y i := of_decide_eq_true (List.mem_filter.1 hi).2
      have fired := (terms_fold _ (tx i) (ts i) D.toList part).1 ⟨term, hm, hall⟩
      have hX := (inX' i).1 fired.2
      by_contra hjn
      have hY : ¬ Y i ⊆ Y n := fun e => hjn (e hjY)
      have gap := step i n hX hY
      have hlt : g (X i) < k := by have := gle (X n); omega
      let t0 : Fin k := ⟨g (X i), hlt⟩
      obtain ⟨L, hL, hpart⟩ := fired.1 t0 (List.mem_filter.2 ⟨List.mem_finRange _, decide_eq_true (le_refl (g (X i)))⟩)
      have hz := (inZ (B t0 \ L)).1 hpart
      apply hesc t0 L (Finset.mem_toList.1 hL) R hR
      intro e he
      by_cases heL : e ∈ L
      · exact Finset.mem_union_left _ heL
      · refine Finset.mem_union_right _ (hup ?_)
        refine Finset.mem_sdiff.2 ⟨hz e (Finset.mem_sdiff.2 ⟨he, heL⟩), fun hh => ?_⟩
        obtain ⟨t, ht, hmem⟩ := (highEq n e).1 hh
        have : t = t0 := by
          by_contra hne
          exact Finset.disjoint_left.1 (hdis _ _ hne) hmem he
        rw [this] at ht
        have : g (X n) ≤ g (X i) := ht
        omega
    · intro hjY
      obtain ⟨term, hm, hall⟩ := (terms_fold (bits (X n) ++ bits z ++ [false,true]) (tx n) (ts n) D.toList part).2 (by
        refine ⟨fun t ht => ⟨L0, Finset.mem_toList.2 hL0, (inZ _).2 (fun e he => ?_)⟩, (inX' n).2 (Finset.Subset.refl _)⟩
        obtain ⟨heB, heL⟩ := Finset.mem_sdiff.1 he
        by_contra hz
        apply heL
        apply hdown
        refine Finset.mem_sdiff.2 ⟨(highEq n e).2 ⟨t, ?_, heB⟩, hz⟩
        exact of_decide_eq_true (List.mem_filter.1 ht).2)
      exact ⟨term, List.mem_flatMap.2 ⟨n, List.mem_filter.2 ⟨List.mem_finRange _, decide_eq_true hjY⟩, hm⟩, hall⟩

end PEqualNP.Outside.L_meta_53186

theorem PEqualNP.Outside.L_meta_53186 : ∀ (m d a b : Nat) (X : Fin m → Finset (Fin d)) (Y : Fin m → Finset (Fin a))
  (D U : Finset (Finset (Fin b))), ∅ ∈ D → ∅ ∈ U →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let bits := fun {n : Nat} (s : Finset (Fin n)) => List.ofFn (fun j => decide (j ∈ s))
  (∃ (P Q : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin b → Nat) (o : Fin a → Nat),
    let high := fun i => (Finset.univ : Finset (Fin b)).filter (fun j =>
      (P.wires (bits (X i) ++ [false,true])).getD (s j) false = false)
    PEqualNP.MetaComplexity.Monotone2 P ∧ PEqualNP.MetaComplexity.Monotone2 Q ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) P ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+b+2) Q ∧
    (∀ j, s j < d+2+P.size) ∧ (∀ j, o j < d+b+2+Q.size) ∧
    ∀ i (z : Finset (Fin b)), (∃ L ∈ D, high i \ z ⊆ L) → (∃ R ∈ U, z \ high i ⊆ R) →
      ∀ j, (Q.wires (bits (X i) ++ bits z ++ [false,true])).getD (o j) false = decide (j ∈ Y i)) ↔
  ∃ (k : Nat) (B : Fin k → Finset (Fin b)),
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, ∀ L ∈ D, ∀ R ∈ U, ¬ B i ⊆ L ∪ R) ∧
    ¬ ∃ lo hi : Fin (k+1) → Fin m,
      (∀ t, X (lo t) ⊆ X (hi t) ∧ ¬ Y (lo t) ⊆ Y (hi t)) ∧
      (∀ t u, t < u → X (hi t) ⊆ X (lo u)) := by
  intro m d a b X Y D U hD hU
  intro bits
  have hb : ∀ {n : ℕ} (s : Finset (Fin n)), bits s = PEqualNP.Outside.L_meta_53186.bits s :=
    fun s => List.ofFn_inj.2 (funext fun j => decide_eq_decide.2 Iff.rfl)
  refine Iff.trans ?_ ((PEqualNP.Outside.L_meta_53186.main m d a b X Y D U hD hU).trans ?_)
  · refine exists_congr fun P => exists_congr fun Q => exists_congr fun s => exists_congr fun o => ?_
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => forall_congr' fun z => ?_
    constructor
    · intro h h1 h2 j
      simp only [hb] at h h1 h2 ⊢
      have := h (by convert h1) (by convert h2) j
      convert this
    · intro h h1 h2 j
      simp only [hb] at h h1 h2 ⊢
      have := h (by convert h1) (by convert h2) j
      convert this
  · refine exists_congr fun k => exists_congr fun B => ?_
    constructor
    · intro h
      convert h
    · intro h
      convert h
