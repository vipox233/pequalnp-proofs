import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20628

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def dep {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

def agree (T : Finset ℕ) (x y : List Bool) : Prop :=
  ∀ i ∈ T, x.getD i false = y.getD i false

def step (x : List Bool) (g : Gate) : List Bool :=
  x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]

theorem len (gs : List Gate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp [step, ih]
    omega

theorem back (n : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (T : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ T.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        agree S x y → agree T (gs.foldl step x) (gs.foldl step y) := by
  induction gs using List.reverseRecOn generalizing T with
  | nil => exact ⟨T, by simp, by intro x y hx hy e; simpa using e⟩
  | append_singleton gs g ih =>
    let p := n + gs.length
    classical
    let M := if p ∈ T then (T.erase p) ∪ g.inputs.toFinset else T
    have hm : M.card ≤ T.card+1 := by
      by_cases hp : p ∈ T
      · rw [show M = T.erase p ∪ g.inputs.toFinset by simp [M,hp]]
        have hu := Finset.card_union_le (T.erase p) g.inputs.toFinset
        have hc := List.toFinset_card_le g.inputs
        have hi := h g (by simp)
        have he := Finset.card_erase_of_mem hp
        have ht : 1 ≤ T.card := Finset.card_pos.mpr ⟨p,hp⟩
        omega
      · simp [M,hp]
    obtain ⟨S, hs, ha⟩ := ih (fun v hv => h v (by simp [hv])) M
    refine ⟨S, by simpa only [List.length_append,List.length_singleton] using
      (show S.card ≤ T.card + (gs.length+1) by omega), ?_⟩
    intro x y hx hy e
    let u := gs.foldl step x
    let v := gs.foldl step y
    have lu : u.length = p := by simp [u,p,len,hx]
    have lv : v.length = p := by simp [v,p,len,hy]
    have hmid : agree M u v := ha x y hx hy e
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
    intro i hit
    change (step u g).getD i false = (step v g).getD i false
    rcases Nat.lt_trichotomy i p with hlt | he | hgt
    · have hi : i ∈ M := by
        by_cases hp : p ∈ T
        · simp [M,hp,hit,show i ≠ p by omega]
        · simp [M,hp,hit]
      rw [step, List.getD_append _ _ _ _ (by omega)]
      rw [step, List.getD_append _ _ _ _ (by omega)]
      exact hmid _ hi
    · subst i
      have harg : g.inputs.map (fun i => u.getD i false) =
          g.inputs.map (fun i => v.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact hmid i (by simp [M,hit,hi])
      have one (w : List Bool) (b : Bool) (hw : w.length = p) :
          (w++[b]).getD p false = b := by rw [← hw]; simp
      simp only [step, one _ _ lu, one _ _ lv, harg]
    · rw [List.getD_eq_default _ _ (by simp [step,lu]; omega),
        List.getD_eq_default _ _ (by simp [step,lv]; omega)]

theorem bound (n : ℕ) (C : Circuit) (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ C.size+1 ∧ dep S (circuitFun n C) := by
  obtain ⟨U, hu, hd⟩ := back n C.gates h {C.output}
  let S : Finset (Fin n) := Finset.univ.filter (fun i => i.val∈U)
  have hi : S.image Fin.val ⊆ U := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hi).2
  have hc := Finset.card_le_card hi
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hc
  refine ⟨S, by simpa [Circuit.size,Nat.add_comm] using hc.trans hu,?_⟩
  intro x y hxy
  have hu' : agree U (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases h : i<n
    · rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn]
      exact hxy ⟨i,h⟩ (by simp [S,hi])
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  exact hd _ _ (by simp) (by simp) hu' C.output (by simp)

open PEqualNP.Represents

private def input {n m : ℕ} (u : Fin n) (v : Fin m) : Fin (n + m) → Bool :=
  Fin.addCases (fun i => decide (i = u)) (fun j => decide (j = v))

private theorem inputList {n m : ℕ} (u : Fin n) (v : Fin m) :
    List.ofFn (input u v) = oneEach u v := by
  rw [List.ofFn_add]
  change List.ofFn (fun i : Fin n => input u v (Fin.castAdd m i)) ++ _ = _
  simp [input, oneEach]

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [ite_eq_right h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]

theorem getD_false_lt {l : List Bool} {t : ℕ} (h : l.getD t false = true) : t < l.length := by
  by_contra h'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

/-- Pointwise order on bit lists, read through `getD`. -/
def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [ite_eq_left h1] at ht ⊢; exact ih t ht
    · rw [ite_eq_right h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [ite_eq_left h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [ite_eq_right h2] at ht; simp at ht

private theorem circuitMono {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true)
    (hx : circuitFun n C x = true) : circuitFun n C y = true := by
  have hr : Le (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases il : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn] at hi ⊢
      exact h ⟨i, il⟩ hi
    · exact False.elim (il (by simpa using getD_false_lt hi))
  exact W_mono C.gates (fun g hg => by simpa using (hm g hg).1) _ _
    (by simp) hr C.output hx

private def graph (u v : Fin 5) : Bool := (25368608 : ℕ).testBit (5 * u.val + v.val)

private theorem forced (C : Circuit) (hm : Monotone2 C) (rep : Represents graph C)
    (S : Finset (Fin 10)) (hd : dep S (circuitFun 10 C))
    (w : Fin 10) (u v u' v' : Fin 5)
    (he : graph u v = true) (hn : graph u' v' = false)
    (cmp : ∀ i : Fin 10, i ≠ w → input u v i = true → input u' v' i = true) :
    w ∈ S := by
  by_contra hw
  let z : Fin 10 → Bool := fun i => if i ∈ S then input u v i else false
  have hz : circuitFun 10 C z = true := by
    rw [hd _ _ (show ∀ i ∈ S, z i = input u v i by intro i hi; simp [z, hi])]
    simpa only [circuitFun, inputList, rep u v] using he
  have hpos : circuitFun 10 C (input u' v') = true := by
    apply circuitMono C hm z _ _ hz
    intro i hi
    by_cases hs : i ∈ S
    · apply cmp i (by intro h; subst i; exact hw hs)
      simpa [z, hs] using hi
    · simp [z, hs] at hi
  simp only [circuitFun, inputList, rep u' v', hn, Bool.false_eq_true] at hpos

end PEqualNP.Outside.L_meta_20628

open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.Outside.L_meta_20628 in
theorem PEqualNP.Outside.L_meta_20628 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25368608 : ℕ).testBit (5 * u.val + v.val)) 8 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25368608 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  constructor
  · exact ⟨⟨[⟨.and, [1, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [16, 15]⟩], 17⟩, by simp [PEqualNP.MetaComplexity.Monotone2], by decide, by decide⟩
  · rintro ⟨C, hm, hsize, rep⟩
    obtain ⟨S, hcard, hd⟩ := bound 10 C (fun g hg => (hm g hg).2)
    let T : Finset (Fin 10) := {1, 2, 3, 4, 5, 6, 7, 8, 9}
    have sub : T ⊆ S := by
      intro i hi
      simp [T] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact forced C hm rep S hd 1 1 0 0 0 (by decide) (by decide) (by decide)
      · exact forced C hm rep S hd 2 2 1 0 1 (by decide) (by decide) (by decide)
      · exact forced C hm rep S hd 3 3 1 0 1 (by decide) (by decide) (by decide)
      · exact forced C hm rep S hd 4 4 3 0 3 (by decide) (by decide) (by decide)
      · exact forced C hm rep S hd 5 1 0 1 1 (by decide) (by decide) (by decide)
      · exact forced C hm rep S hd 6 2 1 2 0 (by decide) (by decide) (by decide)
      · exact forced C hm rep S hd 7 2 2 2 0 (by decide) (by decide) (by decide)
      · exact forced C hm rep S hd 8 4 3 4 0 (by decide) (by decide) (by decide)
      · exact forced C hm rep S hd 9 4 4 4 0 (by decide) (by decide) (by decide)
    have hc := Finset.card_le_card sub
    have ht : T.card = 9 := by decide
    omega
