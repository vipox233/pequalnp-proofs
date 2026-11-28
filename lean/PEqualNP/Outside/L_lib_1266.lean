import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1266_aux

-- Circuit grade argument ported from b2441c058848500d29c9ce2da30b6836f7337a57 at lean/PEqualNP/Outside/L_lib_1228.lean.
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.NotBracket (notCount)

private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1],?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD,ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none noneX,List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases h : g.inputs with
  | nil => simp
  | cons i rest => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i,here,rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit,op,GateOp.eval,List.any_eq_true] at on ⊢
  obtain ⟨v,hm,active⟩ := on
  obtain ⟨i,here,rfl⟩ := List.mem_map.mp hm
  exact ⟨_,List.mem_map.mpr ⟨i,here,rfl⟩,(bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1],if inverting g then 2*s.2+(firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance,neg,ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance,neg] using strict
    exact ⟨increase.le,fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,Bool.false_eq_true,ite_false]
    exact ⟨before.1,fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent,advance,inverting,op,ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega,?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit,op,GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gates : List Gate) : ℕ := (gates.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting,h]

private theorem run_consistent (gates : List Gate) (allowed : ∀ g ∈ gates, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gates.foldl advance s) (gates.foldl advance t) := by
  induction gates generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gates : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2^d) :
    (gates.foldl advance s).2 < 2^(d+negCount gates) := by
  induction gates generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2^(d+1) := by
        simp only [advance,neg,ite_true,Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d+1) raises
      simpa [negCount,neg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2^d := by simpa [advance,neg] using bound
      simpa [negCount,neg] using ih (advance s g) d same

private theorem run_wires (gates : List Gate) (s : List Bool × ℕ) :
    (gates.foldl advance s).1 =
      gates.foldl (fun w g => w ++ [outputBit g w]) s.1 := by
  induction gates generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)

private theorem inputs_order {n : ℕ} {x y : Fin n → Bool} (xy : x ≤ y) :
    bitOrder (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  have first : bitOrder (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro i
    by_cases inside : i < n
    · simpa [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside] using xy ⟨i,inside⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside]
  simpa only [List.append_assoc,List.singleton_append] using
    order_append (order_append first (a := false) (b := false) le_rfl)
      (a := true) (b := true) le_rfl

def grade {n : ℕ} (C : Circuit) (x : Fin n → Bool) : ℕ :=
  (C.gates.foldl advance (List.ofFn x ++ [false,true],0)).2

theorem grade_bound {n : ℕ} (C : Circuit) (x : Fin n → Bool) : grade C x < 2^(notCount C) := by
  simpa [grade,negCount_spec] using
    run_bounded C.gates (List.ofFn x ++ [false,true],0) 0 (by change 0 < 1; decide)

theorem grade_order {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool} (xy : x ≤ y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → ∀ i,
      (C.wires (List.ofFn x ++ [false,true])).getD i false ≤
        (C.wires (List.ofFn y ++ [false,true])).getD i false) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by
    simpa [Allowed] using (basis g mem).1
  have initial : consistent (List.ofFn x ++ [false,true],0) (List.ofFn y ++ [false,true],0) :=
    ⟨le_rfl,fun _ => inputs_order xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1,?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires,run_wires] at order
  exact order

theorem grade_fall {n : ℕ} {C : Circuit} (basis : FanInTwo C) {x y : Fin n → Bool}
    (xy : x ≤ y) (i : ℕ)
    (before : (C.wires (List.ofFn x ++ [false,true])).getD i false = true)
    (after : (C.wires (List.ofFn y ++ [false,true])).getD i false = false) :
    grade C x < grade C y := by
  obtain ⟨order,read⟩ := grade_order basis xy
  refine lt_of_le_of_ne order ?_
  intro eq
  have impossible := read eq i
  rw [before,after] at impossible
  exact (by decide : ¬ (true ≤ false)) impossible

open PEqualNP.CircuitLowerBounds (Circuit)
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

abbrev Graph (n : ℕ) := Fin n → Fin n → Prop
abbrev Answers (n : ℕ) := Finset (Fin n) → Fin n → Bool

abbrev Fits {n : ℕ} (H : Graph n) (g : Answers n) : Prop :=
  (∀ x j, (∀ i ∈ x, H i j) → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)

abbrev Decreasing {n : ℕ} (g : Answers n) : Prop :=
  ∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true

abbrev Runs {n : ℕ} (g : Answers n) : ℕ → Finset (Fin n) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false)

noncomputable abbrev raw {n : ℕ} (x : Finset (Fin n)) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]

abbrev Computes {n : ℕ} (C : Circuit) (g : Answers n) : Prop :=
  FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
    ∃ tap : Fin n → Fin (n+2+C.size),
      ∀ x j, (C.wires (raw x)).getD (tap j).val false = g x j

abbrev Key (d k : ℕ) := {a : Finset (Fin d) // a.card = k}

def KeyGraph {d k n : ℕ} (key : Fin n ≃ Key d k) : Graph n :=
  fun i j => Disjoint (key i).val (key j).val

lemma runs_mono {n : ℕ} {g : Answers n} {r : ℕ} {x y : Finset (Fin n)}
    (xy : x ⊆ y) (hx : Runs g r x) : Runs g r y := by
  cases r with
  | zero => trivial
  | succ r =>
    obtain ⟨u,v,j,hu,uv,vx,ht,hf⟩ := hx
    exact ⟨u,v,j,hu,uv,vx.trans xy,ht,hf⟩

lemma runs_pred {n : ℕ} {g : Answers n} {r : ℕ} {x : Finset (Fin n)}
    (hx : Runs g (r+1) x) : Runs g r x := by
  obtain ⟨u,v,j,hu,uv,vx,_,_⟩ := hx
  exact runs_mono (uv.trans vx) hu

lemma runs_shorten {n : ℕ} {g : Answers n} {r s : ℕ} {x : Finset (Fin n)}
    (rs : r ≤ s) (hx : Runs g s x) : Runs g r x := by
  induction s with
  | zero =>
    have : r = 0 := by omega
    subst r
    trivial
  | succ s ih =>
    rcases Nat.eq_or_lt_of_le rs with rfl | lt
    · exact hx
    · exact ih (by omega) (runs_pred hx)

lemma graph_edge {d k n : ℕ} (key : Fin n ≃ Key d k) (hd : 2*k ≤ d) :
    ∃ i j, KeyGraph key i j := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin d))) (n := k) (by simp; omega)
  have hk : k ≤ aᶜ.card := by simp [Finset.card_compl,ha]; omega
  obtain ⟨b,hb,cb⟩ := Finset.exists_subset_card_eq hk
  refine ⟨key.symm ⟨a,ha⟩, key.symm ⟨b,cb⟩, ?_⟩
  simp only [KeyGraph, Equiv.apply_symm_apply]
  exact disjoint_compl_right.mono_right hb

lemma graph_no_triangle {d k n : ℕ} (key : Fin n ≃ Key d k) (hd : d < 3*k)
    {i j l : Fin n} (ij : KeyGraph key i j) (il : KeyGraph key i l)
    (jl : KeyGraph key j l) : False := by
  classical
  have hu : Disjoint ((key i).val ∪ (key j).val) (key l).val :=
    Finset.disjoint_union_left.mpr ⟨il,jl⟩
  have card := Finset.card_le_univ (((key i).val ∪ (key j).val) ∪ (key l).val)
  rw [Finset.card_union_of_disjoint hu, Finset.card_union_of_disjoint ij,
    (key i).property, (key j).property, (key l).property, Fintype.card_fin] at card
  omega

lemma forced_two {n : ℕ} {H : Graph n} {g : Answers n} (hg : Fits H g)
    (edge : ∃ i j, H i j) : Runs g 2 Finset.univ := by
  obtain ⟨i,j,hij⟩ := edge
  have first : Runs g 1 {i} := by
    refine ⟨∅,{i},i,trivial,Finset.empty_subset _,subset_rfl,?_,?_⟩
    · exact hg.1 _ _ (by simp)
    · exact hg.2 _ _ (by simp)
  refine ⟨{i},insert j {i},j,first,Finset.subset_insert _ _,Finset.subset_univ _,?_,?_⟩
  · exact hg.1 _ _ (by simpa using hij)
  · exact hg.2 _ _ (by simp)

lemma circuit_runs_bound {n : ℕ} {g : Answers n} {C : Circuit} (hc : Computes C g) :
    ∀ r x, Runs g r x → r < 2^(notCount C) := by
  obtain ⟨basis,_,_,tap,htap⟩ := hc
  let input (x : Finset (Fin n)) (i : Fin n) : Bool :=
    @decide (i ∈ x) (Classical.propDecidable (i ∈ x))
  have ordered {x y : Finset (Fin n)} (h : x ⊆ y) : input x ≤ input y := by
    intro i
    apply (bool_order _ _).mpr
    simpa [input] using @h i
  have lower : ∀ r x, Runs g r x → r ≤ grade C (input x) := by
    intro r
    induction r with
    | zero => intro x _; omega
    | succ r ih =>
      intro x hx
      obtain ⟨u,v,j,hu,uv,vx,ht,hf⟩ := hx
      have h₁ := ih u hu
      have h₂ := grade_fall basis (ordered uv) (tap j).val
        ((htap u j).trans ht) ((htap v j).trans hf)
      have h₃ := (grade_order basis (ordered vx)).1
      omega
  intro r x hx
  exact (lower r x hx).trans_lt (grade_bound C (input x))

noncomputable def twoAnswer {n : ℕ} (H : Graph n) (x : Finset (Fin n)) (j : Fin n) : Bool := by
  classical
  exact decide (¬ ∃ i ∈ x, ∃ l ∈ x, H i l) && (decide (x = ∅) || decide (∃ i ∈ x, H i j))

lemma twoAnswer_spec {n : ℕ} (H : Graph n) (x : Finset (Fin n)) (j : Fin n) :
    twoAnswer H x j = true ↔ (¬ ∃ i ∈ x, ∃ l ∈ x, H i l) ∧
      (x = ∅ ∨ ∃ i ∈ x, H i j) := by
  classical
  simp [twoAnswer]

lemma twoAnswer_fits {n : ℕ} (H : Graph n)
    (triangle : ∀ i l j, H i l → H i j → H l j → False) : Fits H (twoAnswer H) := by
  classical
  constructor
  · intro x j h
    apply (twoAnswer_spec H x j).mpr
    refine ⟨?_, ?_⟩
    · rintro ⟨i,hi,l,hl,he⟩
      exact triangle i l j he (h i hi) (h l hl)
    · by_cases hx : x = ∅
      · exact Or.inl hx
      · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hx
        exact Or.inr ⟨i,hi,h i hi⟩
  · intro x j hj
    apply Bool.eq_false_of_not_eq_true
    intro ht
    obtain ⟨no,empty | ⟨i,hi,he⟩⟩ := (twoAnswer_spec H x j).mp ht
    · exact (Finset.notMem_empty j) (empty ▸ hj)
    · exact no ⟨i,hi,j,hj,he⟩

noncomputable def phase {n : ℕ} (H : Graph n) (x : Finset (Fin n)) : ℕ := by
  classical
  exact if (∃ i ∈ x, ∃ l ∈ x, H i l) then 2 else if x = ∅ then 0 else 1

lemma phase_le {n : ℕ} (H : Graph n) (x : Finset (Fin n)) : phase H x ≤ 2 := by
  classical
  unfold phase
  split
  · omega
  · split <;> omega

lemma phase_mono {n : ℕ} (H : Graph n) {x y : Finset (Fin n)} (xy : x ⊆ y) :
    phase H x ≤ phase H y := by
  classical
  have eg : (∃ i ∈ x, ∃ l ∈ x, H i l) → (∃ i ∈ y, ∃ l ∈ y, H i l) := by
    rintro ⟨i,hi,l,hl,he⟩
    exact ⟨i,xy hi,l,xy hl,he⟩
  have em : y = ∅ → x = ∅ := by
    intro hy
    simpa [hy] using xy
  by_cases ey : ∃ i ∈ y, ∃ l ∈ y, H i l
  · simpa [phase, ey] using phase_le H x
  · have ex : ¬ ∃ i ∈ x, ∃ l ∈ x, H i l := fun h => ey (eg h)
    by_cases hy : y = ∅
    · simp [phase,ex,ey,hy,em hy]
    · simp only [phase,ex,ey,hy,ite_false]
      split <;> omega

lemma phase_fall {n : ℕ} (H : Graph n) {x y : Finset (Fin n)} (xy : x ⊆ y) {j : Fin n}
    (ht : twoAnswer H x j = true) (hf : twoAnswer H y j = false) : phase H x < phase H y := by
  classical
  obtain ⟨no,h⟩ := (twoAnswer_spec H x j).mp ht
  have notTrue : ¬ twoAnswer H y j = true := by simp [hf]
  by_cases edge : ∃ i ∈ y, ∃ l ∈ y, H i l
  · simp only [phase, no, edge, ite_false, ite_true]
    split <;> omega
  have ny : y ≠ ∅ := fun ey => notTrue ((twoAnswer_spec H y j).mpr ⟨edge,Or.inl ey⟩)
  rcases h with ex | ⟨i,hi,he⟩
  · simp [phase,edge,ny,ex]
  · exact False.elim (notTrue ((twoAnswer_spec H y j).mpr ⟨edge,Or.inr ⟨i,xy hi,he⟩⟩))

lemma twoAnswer_runs {n : ℕ} (H : Graph n) : ¬ Runs (twoAnswer H) 3 Finset.univ := by
  have bound : ∀ r x, Runs (twoAnswer H) r x → r ≤ phase H x := by
    intro r
    induction r with
    | zero => intro x _; omega
    | succ r ih =>
      intro x hx
      obtain ⟨u,v,j,hu,uv,vx,ht,hf⟩ := hx
      have h₁ := ih u hu
      have h₂ := phase_fall H uv ht hf
      have h₃ := phase_mono H vx
      omega
  intro hx
  have h := bound 3 _ hx
  have lim := phase_le H (Finset.univ : Finset (Fin n))
  omega

noncomputable def color {d : ℕ} (s : ℕ) (x : Finset (Fin d)) : ℕ :=
  (insert s (x.image Fin.val)).min' (Finset.insert_nonempty _ _)

lemma color_le {d : ℕ} (s : ℕ) (x : Finset (Fin d)) : color s x ≤ s :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

lemma color_proper {d k : ℕ} (hk : 0 < k) (hd : 2*k ≤ d)
    {a b : Finset (Fin d)} (ha : a.card = k) (hb : b.card = k) (ab : Disjoint a b) :
    color (d-2*k+1) a ≠ color (d-2*k+1) b := by
  classical
  let s := d-2*k+1
  change color s a ≠ color s b
  intro eq
  have sle : s < d := by dsimp [s]; omega
  by_cases high : color s a = s
  · have high' : color s b = s := eq.symm.trans high
    let i : Fin d := ⟨s,sle⟩
    have sub (x : Finset (Fin d)) (h : color s x = s) : x ⊆ Finset.Ici i := by
      intro p hp
      have incl : p.val ∈ insert s (x.image Fin.val) := Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ hp)
      have m : color s x ≤ p.val := Finset.min'_le _ _ incl
      rw [h] at m
      exact Finset.mem_Ici.mpr m
    have cd := Finset.card_le_card (Finset.union_subset (sub a high) (sub b high'))
    rw [Finset.card_union_of_disjoint ab, ha, hb, Fin.card_Ici] at cd
    change k+k ≤ d-s at cd
    dsimp [s] at cd
    omega
  · have mem (x : Finset (Fin d)) (h : color s x ≠ s) :
        ∃ p ∈ x, p.val = color s x := by
      have m : color s x ∈ insert s (x.image Fin.val) := Finset.min'_mem _ _
      exact Finset.mem_image.mp ((Finset.mem_insert.mp m).resolve_left h)
    obtain ⟨a',ha',ea⟩ := mem a high
    obtain ⟨b',hb',eb⟩ := mem b (fun h => high (eq.trans h))
    have same : a' = b' := Fin.ext (ea.trans (eq.trans eb.symm))
    exact Finset.disjoint_left.mp ab ha' (same ▸ hb')

noncomputable def byColor {n : ℕ} (c : Fin n → ℕ) (x : Finset (Fin n)) (j : Fin n) : Bool := by
  classical
  exact decide (c j ∉ x.image c)

lemma byColor_true {n : ℕ} (c : Fin n → ℕ) (x : Finset (Fin n)) (j : Fin n) :
    byColor c x j = true ↔ c j ∉ x.image c := by
  classical
  simp [byColor]

lemma byColor_complete {n : ℕ} (H : Graph n) (c : Fin n → ℕ) (s : ℕ)
    (proper : ∀ i j, H i j → c i ≠ c j) (cap : ∀ i, c i ≤ s) :
    Fits H (byColor c) ∧ Decreasing (byColor c) ∧ ¬ Runs (byColor c) (s+2) Finset.univ := by
  classical
  have images {x y : Finset (Fin n)} (h : x ⊆ y) : x.image c ⊆ y.image c := Finset.image_subset_image h
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro x j hx
    apply (byColor_true c x j).mpr
    rintro h
    obtain ⟨i,hi,e⟩ := Finset.mem_image.mp h
    exact proper i j (hx i hi) e
  · intro x j hj
    exact Bool.eq_false_of_not_eq_true (fun ht => (byColor_true c x j).mp ht (Finset.mem_image_of_mem _ hj))
  · intro x y h j hj
    exact (byColor_true c x j).mpr (fun hm => (byColor_true c y j).mp hj (images h hm))
  · have count : ∀ r x, Runs (byColor c) r x → r ≤ (x.image c).card := by
      intro r
      induction r with
      | zero => intro x _; omega
      | succ r ih =>
        intro x hx
        obtain ⟨u,v,j,hu,uv,vx,ht,hf⟩ := hx
        have h₁ := ih u hu
        have h₂ : (u.image c).card < (v.image c).card := by
          apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨images uv,?_⟩)
          have vj : c j ∈ v.image c := by
            by_contra no
            have yes := (byColor_true c v j).mpr no
            simp [hf] at yes
          intro e
          exact (byColor_true c u j).mp ht (e ▸ vj)
        have h₃ := Finset.card_le_card (images vx)
        omega
    have sub : (Finset.univ : Finset (Fin n)).image c ⊆ Finset.range (s+1) := by
      intro z hz
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_range.mpr (by have := cap i; omega)
    have lim := Finset.card_le_card sub
    rw [Finset.card_range] at lim
    intro hx
    have h := count _ _ hx
    omega

noncomputable def runLevels {n : ℕ} (g : Answers n) (h : ℕ) (x : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (h+1)).filter (fun r => Runs g r x)

lemma mem_runLevels {n : ℕ} (g : Answers n) (h : ℕ) (x : Finset (Fin n)) (r : ℕ) :
    r ∈ runLevels g h x ↔ r ≤ h ∧ Runs g r x := by
  classical
  simp [runLevels, Nat.lt_succ_iff]

noncomputable def fallRank {n : ℕ} (g : Answers n) (h : ℕ) (x : Finset (Fin n)) : ℕ :=
  (runLevels g h x).max' ⟨0,(mem_runLevels g h x 0).mpr ⟨Nat.zero_le _,trivial⟩⟩

lemma fallRank_spec {n : ℕ} (g : Answers n) (h : ℕ) (x : Finset (Fin n)) :
    fallRank g h x ≤ h ∧ Runs g (fallRank g h x) x :=
  (mem_runLevels g h x _).mp (Finset.max'_mem _ _)

lemma fallRank_ge {n : ℕ} {g : Answers n} {h r : ℕ} {x : Finset (Fin n)}
    (rh : r ≤ h) (hx : Runs g r x) : r ≤ fallRank g h x :=
  Finset.le_max' _ _ ((mem_runLevels g h x r).mpr ⟨rh,hx⟩)

lemma fallRank_mono {n : ℕ} {g : Answers n} {h : ℕ} {x y : Finset (Fin n)}
    (xy : x ⊆ y) : fallRank g h x ≤ fallRank g h y :=
  fallRank_ge (fallRank_spec g h x).1 (runs_mono xy (fallRank_spec g h x).2)

lemma fallRank_empty {n : ℕ} (g : Answers n) (h : ℕ) : fallRank g h ∅ = 0 := by
  by_contra ne
  have hx := runs_shorten (show 1 ≤ fallRank g h ∅ by omega) (fallRank_spec g h ∅).2
  obtain ⟨u,v,j,_,uv,ve,ht,hf⟩ := hx
  have dv : v = ∅ := by simpa using ve
  have du : u = ∅ := by simpa [dv] using uv
  rw [du] at ht
  rw [dv,ht] at hf
  contradiction

lemma fallRank_lt {n : ℕ} {g : Answers n} {h : ℕ} {x y : Finset (Fin n)}
    (bound : ¬ Runs g (h+1) Finset.univ) (xy : x ⊆ y) {j : Fin n}
    (ht : g x j = true) (hf : g y j = false) : fallRank g h x < fallRank g h y := by
  have run : Runs g (fallRank g h x + 1) y :=
    ⟨x,y,j,(fallRank_spec g h x).2,xy,subset_rfl,ht,hf⟩
  apply lt_of_lt_of_le (Nat.lt_succ_self _)
  apply fallRank_ge _ run
  by_contra nle
  exact bound (runs_mono (Finset.subset_univ _) (runs_shorten (by omega) run))

lemma fallRank_stable {n : ℕ} {g : Answers n} {h : ℕ} {x y : Finset (Fin n)}
    (bound : ¬ Runs g (h+1) Finset.univ) (dec : Decreasing g) (xy : x ⊆ y)
    (same : fallRank g h x = fallRank g h y) : g x = g y := by
  funext j
  cases hx : g x j <;> cases hy : g y j
  · rfl
  · exact False.elim (by have := dec x y xy j hy; simp_all)
  · exact False.elim ((fallRank_lt bound xy hx hy).ne same)
  · rfl


open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.NotBracket (notCount)

namespace CircuitUpper

-- The single-gate extension primitives below adapt L_lib_1228.lean, lines 229–441,
-- at b2441c058848500d29c9ce2da30b6836f7337a57.
private def value (C : Circuit) (x : List Bool) (i : Nat) : Bool := (C.wires x).getD i false
private def nextWire (n : Nat) (C : Circuit) : Nat := n + C.size
private def emptyCircuit : Circuit := ⟨[], 0⟩
private def appendGate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩
private def appendNot (C : Circuit) (a : Nat) : Circuit := appendGate C ⟨.not, [a]⟩
private def appendBinary (conj : Bool) (C : Circuit) (a b : Nat) : Circuit :=
  if conj then appendGate C ⟨.and, [a,b]⟩ else appendGate C ⟨.or, [a,b]⟩
private def binaryBit (conj a b : Bool) : Bool := if conj then a && b else a || b
private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

private theorem fold_length (gates : List Gate) (x : List Bool) :
    (gates.foldl gateStep x).length = x.length + gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g rest ih =>
    rw [List.foldl_cons, ih]
    simp [gateStep] <;> omega

private theorem fold_value (gates : List Gate) (x : List Bool) {i : Nat} (h : i < x.length) :
    (gates.foldl gateStep x).getD i false = x.getD i false := by
  induction gates generalizing x with
  | nil => rfl
  | cons g rest ih =>
    have h' : i < (gateStep x g).length := by simp [gateStep]; omega
    rw [List.foldl_cons, ih _ h']
    exact List.getD_append _ _ _ _ h

@[local simp] private theorem appendGate_size (C : Circuit) (g : Gate) :
    (appendGate C g).size = C.size + 1 := by simp [appendGate, Circuit.size]

@[local simp] private theorem appendGate_notCount (C : Circuit) (g : Gate) :
    notCount (appendGate C g) = notCount C +
      (@ite Nat (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op .not) 1 0) := by
  by_cases h : g.op = .not <;> simp [notCount, appendGate, h]

private theorem appendGate_prefix (C : Circuit) (g : Gate) :
    C.gates <+: (appendGate C g).gates := ⟨[g], rfl⟩

private theorem appendGate_fanInTwo {C : Circuit} {g : Gate} (basis : FanInTwo C)
    (op : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (arity : g.inputs.length ≤ 2) : FanInTwo (appendGate C g) := by
  intro k hk
  rcases List.mem_append.mp hk with old | new
  · exact basis k old
  · have same : k = g := List.mem_singleton.mp new
    subst k
    exact ⟨op, arity⟩

private theorem appendGate_readsBack {n : Nat} {C : Circuit} {g : Gate} (valid : ReadsBack n C)
    (inputs : ∀ i ∈ g.inputs, i < nextWire n C) : ReadsBack n (appendGate C g) := by
  intro j hj i hi
  change i ∈ ((C.gates ++ [g]).getD j ⟨.or, []⟩).inputs at hi
  by_cases old : j < C.gates.length
  · rw [List.getD_append _ _ _ _ old] at hi
    exact valid j old i hi
  · change j < (C.gates ++ [g]).length at hj
    have same : j = C.gates.length := by simp at hj; omega
    subst j
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    exact inputs i (by simpa using hi)

private theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = nextWire x.length C := by
  rw [wires_eq]
  exact fold_length C.gates x

private theorem value_of_prefix {C D : Circuit} (ext : C.gates <+: D.gates) {x : List Bool}
    {i : Nat} (h : i < nextWire x.length C) : value D x i = value C x i := by
  obtain ⟨rest, appended⟩ := ext
  simp only [value, wires_eq, ← appended, List.foldl_append]
  apply fold_value
  rw [fold_length]
  exact h

private theorem appendGate_wires (C : Circuit) (g : Gate) (x : List Bool) :
    (appendGate C g).wires x = C.wires x ++ [g.op.eval (g.inputs.map fun i => value C x i)] := by
  simp [appendGate, wires_eq, gateStep, value]

private theorem appendGate_new (C : Circuit) (g : Gate) (x : List Bool) :
    value (appendGate C g) x (nextWire x.length C) =
      g.op.eval (g.inputs.map fun i => value C x i) := by
  rw [value, appendGate_wires, ← wires_length]
  simp [List.getD_eq_getElem?_getD]

private def withConstants {n : Nat} (z : Fin n → Bool) : List Bool := List.ofFn z ++ [false,true]

@[local simp] private theorem withConstants_length {n : Nat} (z : Fin n → Bool) :
    (withConstants z).length = n+2 := by simp [withConstants]

private abbrev good (n : Nat) (C : Circuit) := FanInTwo C ∧ ReadsBack (n+2) C
private abbrev live (n : Nat) (C : Circuit) (i : Nat) := i < nextWire (n+2) C
private abbrev bit {n : Nat} (C : Circuit) (z : Fin n → Bool) (i : Nat) := value C (withConstants z) i

private theorem live_of_prefix {n : Nat} {C D : Circuit} (ext : C.gates <+: D.gates)
    {i : Nat} (h : live n C i) : live n D i :=
  h.trans_le (Nat.add_le_add_left ext.length_le (n+2))

private theorem oldBit {n : Nat} {C D : Circuit} (ext : C.gates <+: D.gates)
    (z : Fin n → Bool) {i : Nat} (h : live n C i) : bit D z i = bit C z i :=
  value_of_prefix ext (by simpa only [withConstants_length] using h)

private theorem inputLive {n : Nat} (C : Circuit) (i : Fin n) : live n C i.val := by
  have hi := i.isLt
  unfold live nextWire
  omega

private theorem falseLive (n : Nat) (C : Circuit) : live n C n := by
  unfold live nextWire
  omega

private theorem inputBit {n : Nat} (C : Circuit) (z : Fin n → Bool) (i : Fin n) :
    bit C z i.val = z i := by
  have h : i.val < (withConstants z).length := by rw [withConstants_length]; omega
  change (C.wires (withConstants z)).getD i.val false = _
  rw [wires_eq, fold_value C.gates _ h]
  have inside : i.val < (List.ofFn z).length := by simpa using i.isLt
  simp only [withConstants, List.getD_eq_getElem?_getD, List.getElem?_append_left inside]
  simp [List.getElem?_ofFn, i.isLt]

private theorem falseBit {n : Nat} (C : Circuit) (z : Fin n → Bool) : bit C z n = false := by
  have h : n < (withConstants z).length := by rw [withConstants_length]; omega
  change (C.wires (withConstants z)).getD n false = _
  rw [wires_eq, fold_value C.gates _ h]
  simp [withConstants, List.getD_eq_getElem?_getD]

private theorem good_empty (n : Nat) : good n emptyCircuit := by
  constructor
  · simp [FanInTwo, emptyCircuit]
  · simp [ReadsBack, emptyCircuit]

private theorem not_extension {n : Nat} {C : Circuit} {a : Nat} (ok : good n C) (ha : live n C a) :
    good n (appendNot C a) ∧ C.gates <+: (appendNot C a).gates ∧
      live n (appendNot C a) (nextWire (n+2) C) ∧
      (∀ z : Fin n → Bool, bit (appendNot C a) z (nextWire (n+2) C) = !bit C z a) := by
  refine ⟨⟨appendGate_fanInTwo (g := ⟨.not,[a]⟩) ok.1 (by simp) (by simp), ?_⟩,
    appendGate_prefix _ _, ?_, ?_⟩
  · apply appendGate_readsBack (g := ⟨.not,[a]⟩) ok.2
    intro i hi
    have h : i = a := List.mem_singleton.mp hi
    subst i
    exact ha
  · simp [live, nextWire, appendNot, Nat.add_assoc]
  · intro z
    simpa [appendNot, GateOp.eval] using appendGate_new C ⟨.not,[a]⟩ (withConstants z)

private theorem binary_extension {n : Nat} {C : Circuit} (conj : Bool) {a b : Nat}
    (ok : good n C) (ha : live n C a) (hb : live n C b) :
    let D := appendBinary conj C a b
    good n D ∧ C.gates <+: D.gates ∧ live n D (nextWire (n+2) C) ∧
      D.size = C.size + 1 ∧ notCount D = notCount C ∧
      (∀ z : Fin n → Bool, bit D z (nextWire (n+2) C) = binaryBit conj (bit C z a) (bit C z b)) := by
  have step (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
      good n (appendGate C ⟨op,[a,b]⟩) := by
    refine ⟨appendGate_fanInTwo ok.1 hop (by simp), appendGate_readsBack ok.2 ?_⟩
    intro i hi
    change i ∈ [a,b] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  cases conj
  · exact ⟨step .or (by simp), appendGate_prefix _ _, by simp [live, nextWire, appendBinary, Nat.add_assoc],
      by simp [appendBinary], by simp [appendBinary], fun z => by
        simpa [appendBinary, binaryBit, GateOp.eval] using appendGate_new C ⟨.or,[a,b]⟩ (withConstants z)⟩
  · exact ⟨step .and (by simp), appendGate_prefix _ _, by simp [live, nextWire, appendBinary, Nat.add_assoc],
      by simp [appendBinary], by simp [appendBinary], fun z => by
        simpa [appendBinary, binaryBit, GateOp.eval] using appendGate_new C ⟨.and,[a,b]⟩ (withConstants z)⟩

private theorem binary_layer_fin {n k : Nat} (conj : Bool) (C : Circuit) (a b : Fin k → Nat)
    (ok : good n C) (hab : ∀ j, live n C (a j) ∧ live n C (b j)) :
    ∃ (D : Circuit) (wire : Fin k → Nat), good n D ∧ C.gates <+: D.gates ∧
      D.size = C.size + k ∧ notCount D = notCount C ∧ (∀ j, live n D (wire j)) ∧
      (∀ z : Fin n → Bool, ∀ j, bit D z (wire j) = binaryBit conj (bit C z (a j)) (bit C z (b j))) := by
  induction k generalizing C with
  | zero => exact ⟨C, Fin.elim0, ok, List.prefix_rfl, (Nat.add_zero _).symm, rfl,
      fun j => Fin.elim0 j, fun _ j => Fin.elim0 j⟩
  | succ k ih =>
    let E := appendBinary conj C (a 0) (b 0)
    obtain ⟨eOK, eExt, eLive, eSize, eNot, eBit⟩ := binary_extension conj ok (hab 0).1 (hab 0).2
    change good n E at eOK
    change C.gates <+: E.gates at eExt
    have restLive (j : Fin k) : live n E (a j.succ) ∧ live n E (b j.succ) :=
      ⟨live_of_prefix eExt (hab j.succ).1, live_of_prefix eExt (hab j.succ).2⟩
    obtain ⟨D, rest, dOK, dExt, dSize, dNot, dLive, dBit⟩ :=
      ih E (fun j => a j.succ) (fun j => b j.succ) eOK restLive
    refine ⟨D, Fin.cases (nextWire (n+2) C) rest, dOK, eExt.trans dExt, ?_,
      dNot.trans eNot, ?_, ?_⟩
    · change E.size = C.size + 1 at eSize
      rw [dSize, eSize]
      omega
    · intro j
      refine Fin.cases ?_ dLive j
      exact live_of_prefix dExt eLive
    · intro z j
      refine Fin.cases ?_ (fun j => ?_) j
      · change bit D z (nextWire (n+2) C) = _
        exact (oldBit dExt z eLive).trans (eBit z)
      · change bit D z (rest j) = _
        rw [dBit z j, oldBit eExt z (hab j.succ).1, oldBit eExt z (hab j.succ).2]

private theorem binary_layer {n : Nat} {α : Type*} [Fintype α] (conj : Bool)
    (C : Circuit) (a b : α → Nat) (ok : good n C)
    (hab : ∀ j, live n C (a j) ∧ live n C (b j)) :
    ∃ (D : Circuit) (wire : α → Nat), good n D ∧ C.gates <+: D.gates ∧
      D.size = C.size + Fintype.card α ∧ notCount D = notCount C ∧ (∀ j, live n D (wire j)) ∧
      (∀ z : Fin n → Bool, ∀ j, bit D z (wire j) = binaryBit conj (bit C z (a j)) (bit C z (b j))) := by
  classical
  let e := Fintype.equivFin α
  obtain ⟨D, wire, dOK, ext, size, cnt, outLive, outBit⟩ :=
    binary_layer_fin conj C (a ∘ e.symm) (b ∘ e.symm) ok (fun j => hab (e.symm j))
  exact ⟨D, wire ∘ e, dOK, ext, size, cnt, fun j => outLive (e j), fun z j => by
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using outBit z (e j)⟩

-- Each input is OR-ed into exactly one bucket. Syncing the other buckets uses
-- the extension invariant, and costs no gates.
private theorem group_or {n : Nat} {α : Type*} [DecidableEq α]
    (tag : Fin n → α) (ids : List (Fin n)) (C : Circuit) (row : α → Nat) (read : Fin n → Nat)
    (ok : good n C) (rowLive : ∀ A, live n C (row A)) (readLive : ∀ i, live n C (read i)) :
    ∃ (D : Circuit) (out : α → Nat), good n D ∧ C.gates <+: D.gates ∧
      D.size = C.size + ids.length ∧ notCount D = notCount C ∧ (∀ A, live n D (out A)) ∧
      (∀ (z : Fin n → Bool) A, bit D z (out A) = true ↔
        bit C z (row A) = true ∨ ∃ i ∈ ids, bit C z (read i) = true ∧ tag i = A) := by
  induction ids generalizing C row with
  | nil => exact ⟨C, row, ok, List.prefix_rfl, by simp, rfl, rowLive, by simp⟩
  | cons i ids ih =>
    let E := appendBinary false C (row (tag i)) (read i)
    let row' : α → Nat := fun A => if tag i = A then nextWire (n+2) C else row A
    obtain ⟨eOK, eExt, eLive, eSize, eNot, eBit⟩ :=
      binary_extension false ok (rowLive (tag i)) (readLive i)
    change good n E at eOK
    change C.gates <+: E.gates at eExt
    change live n E (nextWire (n+2) C) at eLive
    change ∀ z : Fin n → Bool, bit E z (nextWire (n+2) C) =
      binaryBit false (bit C z (row (tag i))) (bit C z (read i)) at eBit
    have rowLive' (A : α) : live n E (row' A) := by
      by_cases h : tag i = A
      · simpa [row', h] using eLive
      · simpa [row', h] using live_of_prefix eExt (rowLive A)
    have readLive' (j : Fin n) : live n E (read j) := live_of_prefix eExt (readLive j)
    obtain ⟨D, out, dOK, dExt, dSize, dNot, dLive, dBit⟩ := ih E row' eOK rowLive' readLive'
    refine ⟨D, out, dOK, eExt.trans dExt, ?_, dNot.trans eNot, dLive, ?_⟩
    · change E.size = C.size + 1 at eSize
      rw [dSize, eSize, List.length_cons]
      omega
    · intro z A
      have reads (j : Fin n) : bit E z (read j) = bit C z (read j) := oldBit eExt z (readLive j)
      have rowBit : bit E z (row' A) = true ↔
          bit C z (row A) = true ∨ (bit C z (read i) = true ∧ tag i = A) := by
        by_cases h : tag i = A
        · subst A
          rw [show row' (tag i) = nextWire (n+2) C by simp [row'], eBit z]
          simp [binaryBit]
        · rw [show row' A = row A by simp [row', h], oldBit eExt z (rowLive A)]
          simp [h]
      rw [dBit z A, rowBit]
      simp only [reads, List.mem_cons]
      constructor
      · rintro ((base | ⟨on, key_eq⟩) | ⟨j, hj, on, key_eq⟩)
        · exact Or.inl base
        · exact Or.inr ⟨i, Or.inl rfl, on, key_eq⟩
        · exact Or.inr ⟨j, Or.inr hj, on, key_eq⟩
      · rintro (base | ⟨j, hj, on, key_eq⟩)
        · exact Or.inl (Or.inl base)
        · rcases hj with rfl | hj
          · exact Or.inl (Or.inr ⟨on, key_eq⟩)
          · exact Or.inr ⟨j, hj, on, key_eq⟩

private def covers {d : Nat} (t A B : Finset (Fin d)) : Prop :=
  B ⊆ A ∧ ∀ a ∈ A, a ∉ B → a ∈ t

private theorem covers_empty {d : Nat} {A B : Finset (Fin d)} : covers ∅ A B ↔ B = A := by
  constructor
  · intro h
    refine Finset.Subset.antisymm h.1 ?_
    intro a ha
    by_contra hna
    exact Finset.notMem_empty a (h.2 a ha hna)
  · rintro rfl
    exact ⟨fun _ h => h, fun a ha hn => (hn ha).elim⟩

private theorem covers_insert {d : Nat} (a : Fin d) (t A B : Finset (Fin d)) :
    covers (insert a t) A B ↔ covers t A B ∨ covers t (A.erase a) B := by
  constructor
  · intro h
    by_cases ha : a ∈ B
    · left
      refine ⟨h.1, fun b hb hnb => ?_⟩
      rcases Finset.mem_insert.mp (h.2 b hb hnb) with rfl | hbt
      · exact (hnb ha).elim
      · exact hbt
    · right
      refine ⟨fun b hb => Finset.mem_erase.mpr ⟨?_, h.1 hb⟩, ?_⟩
      · rintro rfl
        exact ha hb
      · intro b hb hnb
        obtain ⟨hba, hbA⟩ := Finset.mem_erase.mp hb
        exact (Finset.mem_insert.mp (h.2 b hbA hnb)).resolve_left hba
  · rintro (h | h)
    · exact ⟨h.1, fun b hb hnb => Finset.mem_insert_of_mem (h.2 b hb hnb)⟩
    · refine ⟨fun b hb => (Finset.mem_erase.mp (h.1 hb)).2, ?_⟩
      intro b hb hnb
      by_cases hba : b = a
      · exact Finset.mem_insert.mpr (Or.inl hba)
      · exact Finset.mem_insert_of_mem (h.2 b (Finset.mem_erase.mpr ⟨hba, hb⟩) hnb)

-- After processing t, the bucket at A collects the exact keys B contained in A
-- for which A \ B consists only of already processed coordinates.
private theorem subset_layers {d n : Nat} (key : Fin n → Finset (Fin d))
    (t : Finset (Fin d)) (C : Circuit) (row : Finset (Fin d) → Nat) (ok : good n C)
    (rowLive : ∀ A, live n C (row A))
    (rowBit : ∀ (z : Fin n → Bool) A, bit C z (row A) = true ↔ ∃ i, z i = true ∧ key i = A) :
    ∃ (D : Circuit) (out : Finset (Fin d) → Nat), good n D ∧ C.gates <+: D.gates ∧
      D.size = C.size + t.card * 2^d ∧ notCount D = notCount C ∧ (∀ A, live n D (out A)) ∧
      (∀ (z : Fin n → Bool) A, bit D z (out A) = true ↔ ∃ i, z i = true ∧ covers t A (key i)) := by
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨C, row, ok, List.prefix_rfl, by simp, rfl, rowLive, by simpa only [covers_empty] using rowBit⟩
  | insert a t ha ih =>
    obtain ⟨E, prev, eOK, eExt, eSize, eNot, eLive, eBit⟩ := ih
    obtain ⟨D, out, dOK, dExt, dSize, dNot, dLive, dBit⟩ :=
      binary_layer false E prev (fun A => prev (A.erase a)) eOK (fun A => ⟨eLive A, eLive (A.erase a)⟩)
    refine ⟨D, out, dOK, eExt.trans dExt, ?_, dNot.trans eNot, dLive, ?_⟩
    · rw [dSize, eSize, Fintype.card_finset, Fintype.card_fin, Finset.card_insert_of_notMem ha,
        Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    · intro z A
      simp only [dBit z A, binaryBit, Bool.false_eq_true, ite_false, Bool.or_eq_true_iff,
        eBit, covers_insert, and_or_left, exists_or]

private theorem subset_complement_iff {d : Nat} (A B : Finset (Fin d)) :
    A ⊆ Finset.univ \ B ↔ Disjoint A B := by
  rw [Finset.disjoint_left]
  constructor
  · intro h i hi
    exact (Finset.mem_sdiff.mp (h hi)).2
  · intro h i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h hi⟩

private theorem eq_decide_of_iff (b : Bool) (P : Prop) [Decidable P] (h : b = true ↔ P) :
    b = decide P := by
  cases b <;> by_cases hp : P <;> simp [hp] at h ⊢

end CircuitUpper

open CircuitUpper in
theorem circuit_upper {d n : Nat} (key : Fin n → Finset (Fin d)) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (n+2) C ∧ C.output < n+2+C.size ∧
      (∃ tap : Fin n → Fin (n+2+C.size), ∀ (x : Finset (Fin n)) j,
        (C.wires (List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true])).getD (tap j).val false =
          (decide (¬ ∃ i ∈ x, ∃ l ∈ x, Disjoint (key i) (key l)) &&
            (decide (x = ∅) || decide (∃ i ∈ x, Disjoint (key i) (key j))))) ∧
      notCount C = 2 ∧ C.size - 2 ≤ d*2^d + 5*n := by
  obtain ⟨C₁, exactRow, ok₁, _, size₁, cnt₁, live₁, eval₁⟩ :=
    group_or key (List.finRange n) emptyCircuit (fun _ => n) Fin.val (good_empty n)
      (fun _ => falseLive n emptyCircuit) (inputLive emptyCircuit)
  have exactBits (z : Fin n → Bool) (A : Finset (Fin d)) :
      bit C₁ z (exactRow A) = true ↔ ∃ i, z i = true ∧ key i = A := by
    simp only [eval₁, falseBit, Bool.false_eq_true, false_or, List.mem_finRange, true_and, inputBit]
  obtain ⟨C₂, sub, ok₂, _, size₂, cnt₂, live₂, eval₂⟩ :=
    subset_layers key Finset.univ C₁ exactRow ok₁ live₁ exactBits
  have subBits (z : Fin n → Bool) (A : Finset (Fin d)) :
      bit C₂ z (sub A) = true ↔ ∃ i, z i = true ∧ key i ⊆ A := by
    simp [eval₂, covers]
  let nbr (j : Fin n) := sub (Finset.univ \ key j)
  have nbrLive (j : Fin n) : live n C₂ (nbr j) := live₂ _
  have nbrBits (z : Fin n → Bool) (j : Fin n) :
      bit C₂ z (nbr j) = true ↔ ∃ i, z i = true ∧ Disjoint (key i) (key j) := by
    change bit C₂ z (sub (Finset.univ \ key j)) = true ↔ _
    rw [subBits]
    exact exists_congr fun i => and_congr Iff.rfl (subset_complement_iff (key i) (key j))
  obtain ⟨C₃, pair, ok₃, ext₃, size₃, cnt₃, live₃, eval₃⟩ :=
    binary_layer_fin true C₂ Fin.val nbr ok₂ (fun j => ⟨inputLive C₂ j, nbrLive j⟩)
  obtain ⟨C₄, edge, ok₄, ext₄, size₄, cnt₄, live₄, eval₄⟩ :=
    group_or (fun _ : Fin n => ()) (List.finRange n) C₃ (fun _ => n) pair ok₃
      (fun _ => falseLive n C₃) live₃
  have edgeBits (z : Fin n → Bool) : bit C₄ z (edge ()) = true ↔
      ∃ i, z i = true ∧ ∃ l, z l = true ∧ Disjoint (key i) (key l) := by
    simp only [eval₄, falseBit, Bool.false_eq_true, false_or, List.mem_finRange, true_and,
      eq_self, and_true, eval₃, binaryBit, ite_true, Bool.and_eq_true_iff, inputBit, nbrBits]
    constructor <;> rintro ⟨i, hi, l, hl, hd⟩ <;> exact ⟨i, hi, l, hl, hd.symm⟩
  let e := nextWire (n+2) C₄
  let C₅ := appendNot C₄ (sub Finset.univ)
  have univLive : live n C₄ (sub Finset.univ) := live_of_prefix (ext₃.trans ext₄) (live₂ _)
  obtain ⟨ok₅, ext₅, live₅, eval₅⟩ := not_extension ok₄ univLive
  let a := nextWire (n+2) C₅
  let C₆ := appendNot C₅ (edge ())
  have edgeLive : live n C₅ (edge ()) := live_of_prefix ext₅ (live₄ ())
  obtain ⟨ok₆, ext₆, live₆, eval₆⟩ := not_extension ok₅ edgeLive
  have eLive : live n C₆ e := live_of_prefix ext₆ live₅
  have aLive : live n C₆ a := live₆
  have ext₂₆ : C₂.gates <+: C₆.gates := ext₃.trans (ext₄.trans (ext₅.trans ext₆))
  have emptyBit (z : Fin n → Bool) :
      bit C₆ z e = !bit C₂ z (sub Finset.univ) := by
    exact (oldBit ext₆ z live₅).trans ((eval₅ z).trans
      (congrArg Bool.not (oldBit (ext₃.trans ext₄) z (live₂ Finset.univ))))
  have noEdgeBit (z : Fin n → Bool) : bit C₆ z a = !bit C₄ z (edge ()) :=
    (eval₆ z).trans (congrArg Bool.not (oldBit ext₅ z (live₄ ())))
  obtain ⟨C₇, mid, ok₇, ext₇, size₇, cnt₇, live₇, eval₇⟩ :=
    binary_layer_fin false C₆ (fun _ : Fin n => e) nbr ok₆
      (fun j => ⟨eLive, live_of_prefix ext₂₆ (nbrLive j)⟩)
  obtain ⟨C₈, out, ok₈, _, size₈, cnt₈, live₈, eval₈⟩ :=
    binary_layer_fin true C₇ (fun _ : Fin n => a) mid ok₇
      (fun j => ⟨live_of_prefix ext₇ aLive, live₇ j⟩)
  let C : Circuit := ⟨C₈.gates, 0⟩
  refine ⟨C, ok₈.1, ok₈.2, ?_, ⟨fun j => ⟨out j, live₈ j⟩, ?_⟩, ?_, ?_⟩
  · change 0 < n+2+C₈.size
    omega
  · intro x j
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let z : Fin n → Bool := fun i => decide (i ∈ x)
    have edgeDecision : bit C₄ z (edge ()) =
        decide (∃ i ∈ x, ∃ l ∈ x, Disjoint (key i) (key l)) := by
      apply eq_decide_of_iff
      simp [edgeBits, z]
    have nbrDecision : bit C₂ z (nbr j) = decide (∃ i ∈ x, Disjoint (key i) (key j)) := by
      apply eq_decide_of_iff
      simp [nbrBits, z]
    have nonemptyDecision : bit C₂ z (sub Finset.univ) = decide (x ≠ ∅) := by
      apply eq_decide_of_iff
      simpa only [subBits, z, decide_eq_true_eq, Finset.subset_univ, and_true, Finset.nonempty_def] using
        (Finset.nonempty_iff_ne_empty (s := x))
    change bit C₈ z (out j) = _
    rw [eval₈ z j, eval₇ z j, oldBit ext₇ z aLive, oldBit ext₂₆ z (nbrLive j),
      emptyBit, noEdgeBit, nbrDecision, edgeDecision, nonemptyDecision]
    by_cases hx : x = ∅ <;> by_cases he : (∃ i ∈ x, ∃ l ∈ x, Disjoint (key i) (key l)) <;>
      simp [hx, he, binaryBit]
  · change notCount C₈ = 2
    rw [cnt₈, cnt₇]
    change notCount (appendNot (appendNot C₄ (sub Finset.univ)) (edge ())) = 2
    simp only [appendNot, appendGate_notCount, cnt₄, cnt₃, cnt₂, cnt₁] <;> rfl
  · change C₈.size - 2 ≤ d*2^d + 5*n
    have size₅ : C₅.size = C₄.size + 1 :=
      appendGate_size C₄ ⟨.not, [sub Finset.univ]⟩
    have size₆ : C₆.size = C₅.size + 1 :=
      appendGate_size C₅ ⟨.not, [edge ()]⟩
    rw [size₈, size₇, size₆, size₅, size₄, size₃, size₂, size₁]
    simp [emptyCircuit, Circuit.size] <;> omega


/-- Nonempty signed subsets of the ground set. -/
abbrev Signed (d : ℕ) :=
  {ab : Finset (Fin d) × Finset (Fin d) // Disjoint ab.1 ab.2 ∧ (ab.1 ∪ ab.2).Nonempty}

namespace Signed

abbrev pos {d : ℕ} (x : Signed d) : Finset (Fin d) := x.val.1
abbrev neg {d : ℕ} (x : Signed d) : Finset (Fin d) := x.val.2

theorem disjoint {d : ℕ} (x : Signed d) : Disjoint x.pos x.neg := x.property.1

theorem nonempty {d : ℕ} (x : Signed d) : (x.pos ∪ x.neg).Nonempty := x.property.2

def Included {d : ℕ} (x y : Signed d) : Prop := x.pos ⊆ y.pos ∧ x.neg ⊆ y.neg

def flip {d : ℕ} (x : Signed d) : Signed d :=
  ⟨(x.neg, x.pos), x.disjoint.symm, by simpa only [Finset.union_comm] using x.nonempty⟩

@[local simp] theorem flip_pos {d : ℕ} (x : Signed d) : x.flip.pos = x.neg := rfl
@[local simp] theorem flip_neg {d : ℕ} (x : Signed d) : x.flip.neg = x.pos := rfl

private theorem flip_flip {d : ℕ} (x : Signed d) : x.flip.flip = x := by
  apply Subtype.ext
  exact Prod.ext rfl rfl

private theorem flip_mono {d : ℕ} (x y : Signed d) (h : x.Included y) :
    x.flip.Included y.flip := ⟨h.2, h.1⟩

private def embed {d : ℕ} (x : Signed d) : Signed (d + 1) :=
  ⟨(x.pos.map (Fin.succEmb d), x.neg.map (Fin.succEmb d)),
    (Finset.disjoint_map _).2 x.disjoint, by
      obtain ⟨i, hi⟩ := x.nonempty
      refine ⟨i.succ, ?_⟩
      rcases Finset.mem_union.mp hi with hp | hn
      · exact Finset.mem_union_left _ (Finset.mem_map_of_mem (Fin.succEmb d) hp)
      · exact Finset.mem_union_right _ (Finset.mem_map_of_mem (Fin.succEmb d) hn)⟩

private theorem embed_flip {d : ℕ} (x : Signed d) : x.flip.embed = x.embed.flip := rfl

private theorem embed_mono {d : ℕ} (x y : Signed d) (h : x.Included y) :
    x.embed.Included y.embed := ⟨Finset.map_subset_map.2 h.1, Finset.map_subset_map.2 h.2⟩

private def pole (d : ℕ) : Signed (d + 1) :=
  ⟨({0}, ∅), by simp, ⟨0, by simp⟩⟩

private def raised {d : ℕ} (x : Signed d) : Signed (d + 1) :=
  ⟨(insert 0 x.embed.pos, x.embed.neg), by
    refine Finset.disjoint_insert_left.2 ⟨?_, x.embed.disjoint⟩
    intro hz
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hz
    exact Fin.succ_ne_zero i hi,
    ⟨0, Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩⟩

private theorem raised_mono {d : ℕ} (x y : Signed d) (h : x.Included y) :
    x.raised.Included y.raised :=
  ⟨Finset.insert_subset_insert _ (embed_mono x y h).1, (embed_mono x y h).2⟩

private theorem embed_raised {d : ℕ} (x : Signed d) : x.embed.Included x.raised :=
  ⟨Finset.subset_insert _ _, fun _ h => h⟩

private theorem pole_raised {d : ℕ} (x : Signed d) : (pole d).Included x.raised := by
  refine ⟨?_, Finset.empty_subset _⟩
  intro i hi
  obtain rfl := Finset.mem_singleton.mp hi
  exact Finset.mem_insert_self _ _

private theorem pole_refl (d : ℕ) : (pole d).Included (pole d) :=
  ⟨fun _ h => h, fun _ h => h⟩

private theorem included_trans {d : ℕ} {x y z : Signed d} (h : x.Included y)
    (k : y.Included z) : x.Included z :=
  ⟨fun _ hi => k.1 (h.1 hi), fun _ hi => k.2 (h.2 hi)⟩

end Signed

private abbrev Parity := ZMod 2
private abbrev Cochain (α : Type) := List α → Parity

private theorem two_cancel (x : Parity) : x + x = 0 := CharTwo.add_self_eq_zero x

private def pre {α β : Type} (g : α → β) (f : Cochain β) : Cochain α :=
  fun l => f (l.map g)

private theorem pre_add {α β : Type} (g : α → β) (f k : Cochain β) :
    pre g (f + k) = pre g f + pre g k := rfl

-- A cochain boundary adds one face for each deleted position, even for lists with repetitions.
private def bd {α : Type} (f : Cochain α) : List α → Parity
  | [] => 0
  | a :: l => f l + bd (fun s => f (a :: s)) l

private theorem bd_add {α : Type} (f g : Cochain α) (l : List α) :
    bd (f + g) l = bd f l + bd g l := by
  induction l generalizing f g with
  | nil => simp [bd]
  | cons a l ih =>
      change (f l + g l) + bd ((fun s => f (a :: s)) + (fun s => g (a :: s))) l =
        (f l + bd (fun s => f (a :: s)) l) + (g l + bd (fun s => g (a :: s)) l)
      rw [ih]
      abel

private theorem bd_pre {α β : Type} (g : α → β) (f : Cochain β) :
    bd (pre g f) = pre g (bd f) := by
  funext l
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
      change f (l.map g) + bd (pre g (fun s => f (g a :: s))) l =
        f (l.map g) + bd (fun s => f (g a :: s)) (l.map g)
      rw [ih]
      rfl

private theorem bd_bd {α : Type} (f : Cochain α) (l : List α) : bd (bd f) l = 0 := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
      change bd f l + bd (f + bd (fun s => f (a :: s))) l = 0
      rw [bd_add, ih, add_zero, two_cancel]

private theorem bd_congr {α : Type} (f g : Cochain α) (l : List α)
    (h : ∀ s, s.Sublist l → f s = g s) : bd f l = bd g l := by
  induction l generalizing f g with
  | nil => rfl
  | cons a l ih =>
      simp only [bd, h _ (List.sublist_cons_self _ _)]
      congr 1
      exact ih _ _ (fun s hs => h _ (hs.cons_cons a))

private theorem bd_zero {α : Type} (f : Cochain α) (l : List α)
    (h : ∀ s, s.Sublist l → f s = 0) : bd f l = 0 := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
      rw [bd, h _ (List.sublist_cons_self _ _), ih _ (fun s hs => h _ (hs.cons_cons a)), add_zero]

private theorem bd_perm {α : Type} (f : Cochain α)
    (hf : ∀ ⦃l s⦄, l.Perm s → f l = f s) {l s : List α} (h : l.Perm s) :
    bd f l = bd f s := by
  induction h generalizing f with
  | nil => rfl
  | cons a h ih =>
      have hpref : ∀ ⦃u v : List α⦄, u.Perm v → f (a :: u) = f (a :: v) :=
        fun {_ _} hp => hf (List.Perm.cons a hp)
      rw [bd, bd, hf h, ih _ hpref]
  | swap x y l =>
      simp only [bd]
      rw [bd_congr (fun s => f (y :: x :: s)) (fun s => f (x :: y :: s)) l
        (fun s _ => hf (List.Perm.swap x y s))]
      abel
  | trans _ _ ih₁ ih₂ => exact (ih₁ f hf).trans (ih₂ f hf)

private theorem duplicate_perm {α : Type} (l : List α) (h : ¬l.Nodup) :
    ∃ a s, l.Perm (a :: a :: s) := by
  classical
  induction l with
  | nil => exact (h (by simp)).elim
  | cons a l ih =>
      by_cases ha : a ∈ l
      · exact ⟨a, l.erase a, (List.perm_cons_erase ha).cons a⟩
      · have hn : ¬l.Nodup := fun hn => h (List.nodup_cons.2 ⟨ha, hn⟩)
        obtain ⟨b, s, hp⟩ := ih hn
        exact ⟨b, a :: s, (hp.cons a).trans
          ((List.Perm.swap b a (b :: s)).trans ((List.Perm.swap b a s).cons b))⟩

private theorem bd_normal {α : Type} (f : Cochain α)
    (hf : ∀ ⦃l s⦄, l.Perm s → f l = f s) (hn : ∀ l, ¬l.Nodup → f l = 0)
    (l : List α) (h : ¬l.Nodup) : bd f l = 0 := by
  obtain ⟨a, s, hp⟩ := duplicate_perm l h
  rw [bd_perm f hf hp]
  simp only [bd]
  rw [bd_zero _ _ (fun t _ => hn (a :: a :: t) (by simp))]
  rw [add_zero, two_cancel]

-- The prism inserts a single transition from the first vertex map to the second.
private def prism {α β : Type} (g h : α → β) (f : Cochain β) : Cochain α
  | [] => 0
  | a :: l => f (g a :: h a :: l.map h) + prism g h (fun s => f (g a :: s)) l

private theorem prism_add {α β : Type} (g h : α → β) (f k : Cochain β) :
    prism g h (f + k) = prism g h f + prism g h k := by
  funext l
  induction l generalizing f k with
  | nil => simp [prism]
  | cons a l ih =>
      change (f (g a :: h a :: l.map h) + k (g a :: h a :: l.map h)) +
          prism g h ((fun s => f (g a :: s)) + (fun s => k (g a :: s))) l =
        (f (g a :: h a :: l.map h) + prism g h (fun s => f (g a :: s)) l) +
        (k (g a :: h a :: l.map h) + prism g h (fun s => k (g a :: s)) l)
      rw [ih]
      simp only [Pi.add_apply]
      abel

private theorem prism_bd {α β : Type} (g h : α → β) (f : Cochain β) :
    prism g h (bd f) + bd (prism g h f) = pre g f + pre h f := by
  funext l
  induction l generalizing f with
  | nil => change 0 + 0 = f [] + f []; simp only [two_cancel]
  | cons a l ih =>
      let G : Cochain β := fun s => f (g a :: s)
      let M : Parity := bd (fun s => f (g a :: h a :: s)) (l.map h)
      have hp : prism g h (bd f) (a :: l) =
          f (h a :: l.map h) + (G (l.map h) + M) +
            (prism g h f l + prism g h (bd G) l) := by
        change bd f (g a :: h a :: l.map h) + prism g h (f + bd G) l = _
        rw [prism_add]
        rfl
      have hb : bd (prism g h f) (a :: l) =
          prism g h f l + (M + bd (prism g h G) l) := by
        change prism g h f l + bd (pre h (fun s => f (g a :: h a :: s)) + prism g h G) l = _
        rw [bd_add, bd_pre]
        rfl
      have ih' : prism g h (bd G) l + bd (prism g h G) l = G (l.map g) + G (l.map h) := ih G
      change prism g h (bd f) (a :: l) + bd (prism g h f) (a :: l) =
        G (l.map g) + f (h a :: l.map h)
      rw [hp, hb]
      calc
        _ = (prism g h (bd G) l + bd (prism g h G) l) +
            (f (h a :: l.map h) + G (l.map h)) + (M + M) +
            (prism g h f l + prism g h f l) := by abel
        _ = G (l.map g) + f (h a :: l.map h) := by
            rw [ih']
            simp only [two_cancel, add_zero]
            calc
              _ = (G (l.map g) + f (h a :: l.map h)) +
                  (G (l.map h) + G (l.map h)) := by abel
              _ = _ := by rw [two_cancel, add_zero]

private theorem prism_supported {α β : Type} (g h : α → β)
    {R : α → α → Prop} {S : β → β → Prop}
    (gg : ∀ x y, R x y → S (g x) (g y)) (hh : ∀ x y, R x y → S (h x) (h y))
    (gh : ∀ x y, R x y → S (g x) (h y)) (gh₀ : ∀ x, S (g x) (h x))
    (f : Cochain β) (l : List α) (hl : l.Pairwise R)
    (hf : ∀ s : List β, s.length = l.length + 1 → s.Pairwise S →
      (∀ y ∈ s, ∃ x ∈ l, y = g x ∨ y = h x) → f s = 0) : prism g h f l = 0 := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
      obtain ⟨ha, hl⟩ := List.pairwise_cons.mp hl
      have hfront : f (g a :: h a :: l.map h) = 0 := by
        apply hf _ (by simp)
        · refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.Pairwise.map h hh hl⟩⟩
          · intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact gh₀ a
            · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
              exact gh _ _ (ha _ hx)
          · intro y hy
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
            exact hh _ _ (ha _ hx)
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨a, by simp, Or.inl rfl⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨a, by simp, Or.inr rfl⟩
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
          exact ⟨x, List.mem_cons_of_mem _ hx, Or.inr rfl⟩
      have hrest : prism g h (fun s => f (g a :: s)) l = 0 := by
        apply ih _ hl
        intro s hlen hs hm
        apply hf _ (by simp only [List.length_cons]; omega)
        · refine List.pairwise_cons.2 ⟨?_, hs⟩
          intro y hy
          obtain ⟨x, hx, rfl | rfl⟩ := hm y hy
          · exact gg _ _ (ha _ hx)
          · exact gh _ _ (ha _ hx)
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨a, by simp, Or.inl rfl⟩
          · obtain ⟨x, hx, hy⟩ := hm y hy
            exact ⟨x, List.mem_cons_of_mem _ hx, hy⟩
      simp only [prism, hfront, hrest, add_zero]

-- The equator lies below the raised map, as does the constant positive pole.
private def coneStep {d : ℕ} (f : Cochain (Signed (d + 1))) : Cochain (Signed d) :=
  prism Signed.embed Signed.raised f + prism (fun _ => Signed.pole d) Signed.raised f

private theorem coneStep_add {d : ℕ} (f k : Cochain (Signed (d + 1))) :
    coneStep (f + k) = coneStep f + coneStep k := by
  funext l
  simp only [coneStep, prism_add, Pi.add_apply]
  abel

private theorem coneStep_bd {d : ℕ} (f : Cochain (Signed (d + 1))) :
    coneStep (bd f) + bd (coneStep f) = pre Signed.embed f + pre (fun _ => Signed.pole d) f := by
  let p := prism (@Signed.embed d) (@Signed.raised d)
  let q := prism (fun _ : Signed d => Signed.pole d) (@Signed.raised d)
  change (p (bd f) + q (bd f)) + bd (p f + q f) = _
  rw [show bd (p f + q f) = bd (p f) + bd (q f) from funext (bd_add _ _)]
  calc
    _ = (p (bd f) + bd (p f)) + (q (bd f) + bd (q f)) := by
      funext l
      simp only [Pi.add_apply]
      abel
    _ = _ := by
      have hp : p (bd f) + bd (p f) = pre Signed.embed f + pre Signed.raised f :=
        prism_bd _ _ _
      have hq : q (bd f) + bd (q f) = pre (fun _ => Signed.pole d) f + pre Signed.raised f :=
        prism_bd _ _ _
      rw [hp, hq]
      funext l
      simp only [Pi.add_apply]
      calc
        _ = (pre Signed.embed f l + pre (fun _ => Signed.pole d) f l) +
            (pre Signed.raised f l + pre Signed.raised f l) := by abel
        _ = _ := by rw [two_cancel, add_zero]

private theorem coneStep_supported {d : ℕ} (f : Cochain (Signed (d + 1)))
    (l : List (Signed d)) (hl : l.Pairwise Signed.Included)
    (hf : ∀ s : List (Signed (d + 1)), s.length = l.length + 1 →
      s.Pairwise Signed.Included → f s = 0) : coneStep f l = 0 := by
  have hp : prism Signed.embed Signed.raised f l = 0 :=
    prism_supported _ _ Signed.embed_mono Signed.raised_mono
      (fun x y h => Signed.included_trans (Signed.embed_mono x y h) (Signed.embed_raised y))
      Signed.embed_raised f l hl (fun s h hs _ => hf s h hs)
  have hq : prism (fun _ : Signed d => Signed.pole d) Signed.raised f l = 0 :=
    prism_supported _ _ (fun _ _ _ => Signed.pole_refl d) Signed.raised_mono
      (fun _ y _ => Signed.pole_raised y) Signed.pole_raised f l hl (fun s h hs _ => hf s h hs)
  simp only [coneStep, Pi.add_apply, hp, hq, add_zero]

-- These functionals represent a hemisphere chain and the sum of its antipodal translates.
private def hemi : (d : ℕ) → Cochain (Signed d) → Parity
  | 0, _ => 0
  | 1, f => f [Signed.pole 0]
  | n + 2, f => hemi (n + 1) (coneStep f) + hemi (n + 1) (pre Signed.flip (coneStep f))

private def sphere (d : ℕ) (f : Cochain (Signed d)) : Parity :=
  hemi d f + hemi d (pre Signed.flip f)

private theorem hemi_add (d : ℕ) (f k : Cochain (Signed d)) :
    hemi d (f + k) = hemi d f + hemi d k := by
  induction d with
  | zero => simp [hemi]
  | succ d ih =>
      cases d with
      | zero => rfl
      | succ n =>
          simp only [hemi, coneStep_add, pre_add, ih]
          abel

private theorem sphere_add (d : ℕ) (f k : Cochain (Signed d)) :
    sphere d (f + k) = sphere d f + sphere d k := by
  simp only [sphere, pre_add, hemi_add]
  abel

private theorem sphere_flip {d : ℕ} (f : Cochain (Signed d)) :
    sphere d (pre Signed.flip f) = sphere d f := by
  have hh : pre Signed.flip (pre Signed.flip f) = f := by
    funext l
    change f ((l.map Signed.flip).map Signed.flip) = f l
    simp [Function.comp_def, Signed.flip_flip]
  simp only [sphere, hh]
  exact add_comm _ _

private theorem sphere_const {d e : ℕ} (x : Signed e) (f : Cochain (Signed e)) :
    sphere d (pre (fun _ : Signed d => x) f) = 0 := by
  have hh : pre Signed.flip (pre (fun _ : Signed d => x) f) = pre (fun _ => x) f := by
    funext l
    simp [pre, Function.comp_def]
  simp only [sphere, hh, two_cancel]

private theorem hemi_boundary {n : ℕ} (f : Cochain (Signed (n + 2)))
    (cycle : ∀ g, sphere (n + 1) (bd g) = 0) :
    hemi (n + 2) (bd f) = sphere (n + 1) (pre Signed.embed f) := by
  have hh := congrArg (sphere (n + 1)) (coneStep_bd f)
  rw [sphere_add, cycle, add_zero, sphere_add, sphere_const, add_zero] at hh
  exact hh

private theorem sphere_cycle (d : ℕ) (f : Cochain (Signed d)) : sphere d (bd f) = 0 := by
  induction d with
  | zero => simp [sphere, hemi]
  | succ d ih =>
      cases d with
      | zero =>
          change (f [] + 0) + (f [] + 0) = 0
          simp only [add_zero, two_cancel]
      | succ n =>
          have hh : pre Signed.embed (pre Signed.flip f) = pre Signed.flip (pre Signed.embed f) := by
            funext l
            simp [pre, Function.comp_def, Signed.embed_flip]
          unfold sphere
          rw [← bd_pre, hemi_boundary f ih, hemi_boundary _ ih, hh, sphere_flip, two_cancel]

-- Evaluation only sees lists of the specified length that are chains in the signed-set poset.
private theorem hemi_supported (d : ℕ) (f k : Cochain (Signed d))
    (hfk : ∀ l : List (Signed d), l.length = d → l.Pairwise Signed.Included → f l = k l) :
    hemi d f = hemi d k := by
  induction d with
  | zero => rfl
  | succ d ih =>
      cases d with
      | zero => exact hfk _ rfl (List.pairwise_singleton _ _)
      | succ n =>
          have hs : ∀ l : List (Signed (n + 1)), l.length = n + 1 →
              l.Pairwise Signed.Included → coneStep f l = coneStep k l := by
            intro l hlen hl
            have hz := coneStep_supported (f + k) l hl (fun s hs hp => by
              simp only [Pi.add_apply, hfk s (by omega) hp, two_cancel])
            rw [coneStep_add] at hz
            change coneStep f l + coneStep k l = 0 at hz
            calc
              coneStep f l = (coneStep f l + coneStep k l) + coneStep k l := by
                rw [add_assoc, two_cancel, add_zero]
              _ = coneStep k l := by rw [hz, zero_add]
          simp only [hemi]
          rw [ih _ _ hs]
          congr 1
          apply ih
          intro l hlen hl
          exact hs (l.map Signed.flip) (by simpa using hlen)
            (List.Pairwise.map _ Signed.flip_mono hl)

private theorem sphere_supported {d : ℕ} (f k : Cochain (Signed d))
    (hfk : ∀ l : List (Signed d), l.length = d → l.Pairwise Signed.Included → f l = k l) :
    sphere d f = sphere d k := by
  unfold sphere
  rw [hemi_supported _ _ _ hfk]
  congr 1
  apply hemi_supported
  intro l hlen hl
  exact hfk (l.map Signed.flip) (by simpa using hlen)
    (List.Pairwise.map _ Signed.flip_mono hl)

private theorem sphere_zero (d : ℕ) : sphere d 0 = 0 := by
  have h := sphere_add d 0 0
  simpa only [zero_add, two_cancel] using h

private abbrev Label (m : ℕ) := Bool × Fin m
private def opposite {m : ℕ} (a : Label m) : Label m := (!a.1, a.2)
private def compatible {m : ℕ} (a b : Label m) : Prop := a.2 = b.2 → a.1 = b.1

private theorem compatible_all {m : ℕ} {l : List (Label m)} (hl : l.Pairwise compatible)
    {a b : Label m} (ha : a ∈ l) (hb : b ∈ l) : compatible a b := by
  induction l with
  | nil => cases ha
  | cons x l ih =>
      obtain ⟨hx, ht⟩ := List.pairwise_cons.mp hl
      rcases List.mem_cons.mp ha with ea | hta <;> rcases List.mem_cons.mp hb with eb | htb
      · rw [ea, eb]
        exact fun _ => rfl
      · rw [ea]
        exact hx _ htb
      · rw [eb]
        exact fun e => (hx _ hta e.symm).symm
      · exact ih ht hta htb

private def chosen {m : ℕ} (l : List (Label m)) : Prop :=
  ∃ a ∈ l, a.1 = true ∧ ∀ b ∈ l, a.2 ≤ b.2

private theorem chosen_perm {m : ℕ} {l s : List (Label m)} (h : l.Perm s) :
    chosen l ↔ chosen s := by
  constructor <;> rintro ⟨a, ha, hs, hmin⟩
  · exact ⟨a, h.mem_iff.mp ha, hs, fun b hb => hmin b (h.mem_iff.mpr hb)⟩
  · exact ⟨a, h.mem_iff.mpr ha, hs, fun b hb => hmin b (h.mem_iff.mp hb)⟩

private theorem minimum_label {m : ℕ} (l : List (Label m)) (hne : l ≠ []) :
    ∃ a ∈ l, ∀ b ∈ l, a.2 ≤ b.2 := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons x l ih =>
      by_cases h : l = []
      · subst l
        exact ⟨x, by simp, by simp⟩
      · obtain ⟨a, ha, hmin⟩ := ih h
        by_cases e : x.2 ≤ a.2
        · refine ⟨x, by simp, ?_⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact le_rfl
          · exact e.trans (hmin b hb)
        · refine ⟨a, List.mem_cons_of_mem _ ha, ?_⟩
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact le_of_not_ge e
          · exact hmin b hb

private theorem chosen_iff_sign {m : ℕ} {l : List (Label m)} (hl : l.Pairwise compatible)
    {a : Label m} (ha : a ∈ l) (hmin : ∀ b ∈ l, a.2 ≤ b.2) :
    chosen l ↔ a.1 = true := by
  constructor
  · rintro ⟨b, hb, hsign, hm⟩
    exact (compatible_all hl ha hb (le_antisymm (hmin b hb) (hm a ha))).trans hsign
  · exact fun h => ⟨a, ha, h, hmin⟩

private theorem chosen_flip {m : ℕ} {l : List (Label m)} (hl : l.Pairwise compatible)
    (hne : l ≠ []) : chosen (l.map opposite) ↔ ¬chosen l := by
  obtain ⟨a, ha, hmin⟩ := minimum_label l hne
  have hp : (l.map opposite).Pairwise compatible :=
    List.Pairwise.map opposite (fun x y (h : compatible x y) e => congrArg (fun b => !b) (h e)) hl
  have hap : opposite a ∈ l.map opposite := List.mem_map_of_mem ha
  have hmp : ∀ b ∈ l.map opposite, (opposite a).2 ≤ b.2 := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact hmin x hx
  rw [chosen_iff_sign hp hap hmp, chosen_iff_sign hl ha hmin]
  change (!a.1) = true ↔ ¬ a.1 = true
  cases a.1 <;> decide

-- Split the invariant boundary cochain into its two antipodal halves at each degree.
private noncomputable def target {m : ℕ} : ℕ → Cochain (Label m)
  | 0, l => if l = [] then 1 else 0
  | n + 1, l => by
      classical
      exact if chosen l then bd (target n) l else 0

private theorem target_perm {m n : ℕ} {l s : List (Label m)} (h : l.Perm s) :
    target n l = target n s := by
  induction n generalizing l s with
  | zero =>
      have e : l = [] ↔ s = [] := by
        constructor
        · intro e
          subst l
          exact h.symm.eq_nil
        · intro e
          subst s
          exact h.eq_nil
      simp only [target, e]
  | succ n ih =>
      classical
      have hbd : bd (target n) l = bd (target n) s :=
        bd_perm _ (fun {_ _} hp => ih hp) h
      simp only [target, chosen_perm h, hbd]

private theorem target_normal {m n : ℕ} (l : List (Label m)) (h : ¬l.Nodup) :
    target n l = 0 := by
  induction n generalizing l with
  | zero => cases l <;> simp_all [target]
  | succ n ih =>
      classical
      have hbd : bd (target n) l = 0 :=
        bd_normal _ (fun {_ _} hp => target_perm hp) ih _ h
      simp only [target, hbd, ite_self]

private theorem target_split_of_invariant {m n : ℕ} (l : List (Label m))
    (hl : l.Pairwise compatible) (hbd : bd (target n) (l.map opposite) = bd (target n) l) :
    target (n + 1) l + target (n + 1) (l.map opposite) = bd (target n) l := by
  classical
  by_cases he : l = []
  · subst l
    simp [target, chosen, bd]
  · change (if chosen l then bd (target n) l else 0) +
      (if chosen (l.map opposite) then bd (target n) (l.map opposite) else 0) = bd (target n) l
    by_cases hc : chosen l
    · rw [if_pos hc, if_neg (fun h => (chosen_flip hl he).mp h hc), add_zero]
    · rw [if_neg hc, if_pos ((chosen_flip hl he).mpr hc), zero_add, hbd]

private theorem target_split {m : ℕ} (n : ℕ) (l : List (Label m))
    (hl : l.Pairwise compatible) :
    target (n + 1) l + target (n + 1) (l.map opposite) = bd (target n) l := by
  induction n generalizing l with
  | zero =>
      have inv : pre opposite (target (m := m) 0) = target 0 := by
        funext s
        simp [pre, target]
      have hbd : bd (target 0) (l.map opposite) = bd (target 0) l := by
        change pre opposite (bd (target 0)) l = _
        rw [← bd_pre, inv]
      exact target_split_of_invariant l hl hbd
  | succ n ih =>
      have hinv : bd (target (n + 1)) l + bd (target (n + 1)) (l.map opposite) = 0 := by
        change bd (target (n + 1)) l + pre opposite (bd (target (n + 1))) l = 0
        rw [← bd_pre, ← bd_add]
        calc
          _ = bd (bd (target n)) l := bd_congr _ _ _ (fun s hs => ih s (hl.sublist hs))
          _ = 0 := bd_bd _ _
      have hbd : bd (target (n + 1)) (l.map opposite) = bd (target (n + 1)) l := by
        calc
          _ = bd (target (n + 1)) l +
              (bd (target (n + 1)) l + bd (target (n + 1)) (l.map opposite)) := by
                rw [← add_assoc, two_cancel, zero_add]
          _ = _ := by rw [hinv, add_zero]
      exact target_split_of_invariant l hl hbd

private theorem sphere_target {m : ℕ} (d : ℕ) (label : Signed (d + 1) → Label m)
    (anti : ∀ x, label x.flip = opposite (label x))
    (ok : ∀ x y, x.Included y → compatible (label x) (label y)) :
    sphere (d + 1) (pre label (target (d + 1))) = 1 := by
  induction d with
  | zero =>
      change target 1 [label (Signed.pole 0)] + target 1 [label (Signed.pole 0).flip] = 1
      rw [anti]
      exact (target_split 0 [label (Signed.pole 0)] (List.pairwise_singleton _ _)).trans
        (by simp [bd, target])
  | succ n ih =>
      let D := n + 2
      let F : Cochain (Label m) := target D
      let E : Cochain (Label m) := target (n + 1)
      have hsum : hemi D (pre label F) + hemi D (pre Signed.flip (pre label F)) =
          hemi D (bd (pre label E)) := by
        rw [← hemi_add, bd_pre]
        apply hemi_supported
        intro l _ hl
        have hm : (l.map Signed.flip).map label = (l.map label).map opposite := by
          simpa only [List.map_map, Function.comp_apply] using
            (List.map_congr_left (l := l) (fun x _ => anti x) :
              l.map (label ∘ Signed.flip) = l.map (opposite ∘ label))
        change F (l.map label) + F ((l.map Signed.flip).map label) = bd E (l.map label)
        rw [hm]
        exact target_split (n + 1) _ (List.Pairwise.map label ok hl)
      change hemi D (pre label F) + hemi D (pre Signed.flip (pre label F)) = 1
      rw [hsum, hemi_boundary _ (sphere_cycle _)]
      have hh : pre Signed.embed (pre label E) = pre (label ∘ Signed.embed) E := by
        funext l
        simp [pre]
      rw [hh]
      exact ih (label ∘ Signed.embed)
        (fun x => by simpa only [Function.comp_apply, Signed.embed_flip] using anti x.embed)
        (fun x y h => ok _ _ (Signed.embed_mono x y h))

/-- The signed-set form of Tucker's lemma. Equal magnitudes on comparable signed sets must
have equal signs, while the antipodal map reverses the sign. -/
theorem signed_tucker {d m : ℕ} (label : Signed d → Bool × Fin m)
    (anti : ∀ x, label x.flip = (!(label x).1, (label x).2))
    (consistent : ∀ x y, x.Included y → (label x).2 = (label y).2 → (label x).1 = (label y).1) :
    d ≤ m := by
  cases d with
  | zero => exact Nat.zero_le _
  | succ n =>
      by_contra! h
      have hv := sphere_target n label anti consistent
      have hz : sphere (n + 1) (pre label (target (n + 1))) = sphere (n + 1) 0 := by
        apply sphere_supported
        intro l hlen hl
        have hc : (l.map label).Pairwise compatible := List.Pairwise.map label consistent hl
        change target (n + 1) (l.map label) = 0
        apply target_normal
        intro hn
        have hh : ((l.map label).map Prod.snd).Nodup :=
          hn.map_on (fun _ ha _ hb e => Prod.ext (compatible_all hc ha hb e) e)
        have hm := hh.length_le_card
        simpa only [List.length_map, Fintype.card_fin, hlen, not_le.mpr h] using hm
      rw [sphere_zero] at hz
      exact zero_ne_one (hz.symm.trans hv)


noncomputable def keyIndices {d k n : ℕ} (key : Fin n ≃ Key d k) (a : Finset (Fin d)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => (key i).val ⊆ a)

lemma mem_keyIndices {d k n : ℕ} (key : Fin n ≃ Key d k) (a : Finset (Fin d)) (i : Fin n) :
    i ∈ keyIndices key a ↔ (key i).val ⊆ a := by
  classical
  simp [keyIndices]

lemma keyIndices_mono {d k n : ℕ} (key : Fin n ≃ Key d k) {a b : Finset (Fin d)}
    (ab : a ⊆ b) : keyIndices key a ⊆ keyIndices key b := by
  intro i hi
  exact (mem_keyIndices key b i).mpr (((mem_keyIndices key a i).mp hi).trans ab)

lemma keyIndices_nonempty {d k n : ℕ} (key : Fin n ≃ Key d k) (a : Finset (Fin d)) :
    (keyIndices key a).Nonempty ↔ k ≤ a.card := by
  classical
  constructor
  · rintro ⟨i,hi⟩
    have h := Finset.card_le_card ((mem_keyIndices key a i).mp hi)
    rwa [(key i).property] at h
  · intro h
    obtain ⟨s,sa,sc⟩ := Finset.exists_subset_card_eq h
    refine ⟨key.symm ⟨s,sc⟩, (mem_keyIndices key a _).mpr ?_⟩
    simpa only [Equiv.apply_symm_apply] using sa

lemma keyIndices_empty {d k n : ℕ} (key : Fin n ≃ Key d k) {a : Finset (Fin d)}
    (small : a.card < k) : keyIndices key a = ∅ := by
  by_contra ne
  exact (not_le_of_gt small) ((keyIndices_nonempty key a).mp (Finset.nonempty_iff_ne_empty.mpr ne))

lemma keyIndices_true {d k n : ℕ} {key : Fin n ≃ Key d k} {g : Answers n}
    (hg : Fits (KeyGraph key) g) {a b : Finset (Fin d)} (ab : Disjoint a b)
    {j : Fin n} (hj : j ∈ keyIndices key b) : g (keyIndices key a) j = true := by
  apply hg.1
  intro i hi
  exact ab.mono ((mem_keyIndices key a i).mp hi) ((mem_keyIndices key b j).mp hj)

noncomputable def orderSign {α : Type*} [Fintype α] (a b : α) : Bool := by
  classical
  exact decide (Fintype.equivFin α a < Fintype.equivFin α b)

lemma orderSign_swap {α : Type*} [Fintype α] {a b : α} (ne : a ≠ b) :
    orderSign b a = !orderSign a b := by
  classical
  have ne' : Fintype.equivFin α a ≠ Fintype.equivFin α b :=
    fun eq => ne ((Fintype.equivFin α).injective eq)
  rcases lt_or_gt_of_ne ne' with lt | gt
  · simp [orderSign,lt,lt.not_gt]
  · simp [orderSign,gt,gt.not_gt]

set_option maxHeartbeats 600000 in
lemma decreasing_bound {d k n h : ℕ} (key : Fin n ≃ Key d k) (hk : 0 < k) (hd : 2*k ≤ d)
    {g : Answers n} (hg : Fits (KeyGraph key) g) (dec : Decreasing g)
    (bound : ¬ Runs g (h+1) Finset.univ) : d+4 ≤ 2*k+2*h := by
  classical
  have hh : 2 ≤ h := by
    by_contra nh
    exact bound (runs_shorten (by omega) (forced_two hg (graph_edge key hd)))
  let X := keyIndices key
  let R := fallRank g h
  let small (z : Signed d) := z.pos.card < k ∧ z.neg.card < k
  let size (z : Signed d) := z.pos.card + z.neg.card
  let score (z : Signed d) := R (X z.pos) + R (X z.neg)
  have zero {a : Finset (Fin d)} (ha : a.card < k) : R (X a) = 0 := by
    change fallRank g h (keyIndices key a) = 0
    rw [keyIndices_empty key ha, fallRank_empty]
  have high (z : Signed d) (hz : ¬ small z) : 0 < score z := by
    have positive (a : Finset (Fin d)) (ha : k ≤ a.card) : 0 < R (X a) := by
      obtain ⟨j,hj⟩ := (keyIndices_nonempty key a).mpr ha
      have lt := fallRank_lt bound (Finset.empty_subset (X a)) (hg.1 ∅ j (by simp)) (hg.2 _ _ hj)
      rwa [fallRank_empty] at lt
    by_cases hp : z.pos.card < k
    · have hn := positive z.neg (Nat.le_of_not_gt (fun hn => hz ⟨hp,hn⟩))
      dsimp [score]; omega
    · have hp' := positive z.pos (Nat.le_of_not_gt hp)
      dsimp [score]; omega
  have high_le (z : Signed d) : score z ≤ 2*h-2 := by
    have cap (a : Finset (Fin d)) : R (X a) ≤ h := (fallRank_spec g h (X a)).1
    have strict {a b : Finset (Fin d)} (ab : Disjoint a b) (hb : k ≤ b.card) : R (X a) < h := by
      obtain ⟨j,hj⟩ := (keyIndices_nonempty key b).mpr hb
      have lt := fallRank_lt bound (Finset.subset_insert j (X a)) (keyIndices_true hg ab hj)
        (hg.2 _ _ (Finset.mem_insert_self _ _))
      exact lt.trans_le (fallRank_spec g h (insert j (X a))).1
    by_cases hp : z.pos.card < k
    · dsimp [score]; rw [zero hp]; have := cap z.neg; omega
    by_cases hn : z.neg.card < k
    · dsimp [score]; rw [zero hn]; have := cap z.pos; omega
    · have p := strict z.disjoint (Nat.le_of_not_gt hn)
      have n := strict z.disjoint.symm (Nat.le_of_not_gt hp)
      dsimp [score]; omega
  have size_pos (z : Signed d) : 0 < size z := by
    have nn := Finset.card_pos.mpr z.nonempty
    rw [Finset.card_union_of_disjoint z.disjoint] at nn
    exact nn
  have size_cap (z : Signed d) (hz : small z) : size z ≤ 2*k-2 := by
    obtain ⟨hp,hn⟩ := hz
    dsimp [size]; omega
  have base_ne (z : Signed d) : z.pos ≠ z.neg := by
    intro eq
    obtain ⟨u,hu⟩ := z.nonempty
    have p : u ∈ z.pos := by simpa [eq] using hu
    exact Finset.disjoint_left.mp z.disjoint p (eq ▸ p)
  have vectors_ne (z : Signed d) (hz : ¬ small z) : g (X z.pos) ≠ g (X z.neg) := by
    intro eq
    by_cases hp : z.pos.card < k
    · obtain ⟨j,hj⟩ := (keyIndices_nonempty key z.neg).mpr
        (Nat.le_of_not_gt (fun hn => hz ⟨hp,hn⟩))
      have ht := keyIndices_true hg z.disjoint hj
      have hf := hg.2 _ _ hj
      rw [eq,hf] at ht
      contradiction
    · obtain ⟨j,hj⟩ := (keyIndices_nonempty key z.pos).mpr (Nat.le_of_not_gt hp)
      have ht := keyIndices_true hg z.disjoint.symm hj
      have hf := hg.2 _ _ hj
      rw [← eq,hf] at ht
      contradiction
  let m := 2*k-2 + (2*h-2)
  let label (z : Signed d) : Bool × Fin m :=
    if hz : small z then
      (orderSign z.pos z.neg, ⟨size z - 1, by have := size_pos z; have := size_cap z hz; dsimp [m]; omega⟩)
    else
      (orderSign (g (X z.pos)) (g (X z.neg)),
        ⟨2*k-2 + (score z - 1), by have := high z hz; have := high_le z; dsimp [m]; omega⟩)
  have anti (z : Signed d) : label z.flip = (!(label z).1, (label z).2) := by
    have flip_small : small z.flip ↔ small z := by change (_ ∧ _) ↔ (_ ∧ _); exact and_comm
    by_cases hz : small z
    · simp only [label, dif_pos hz, dif_pos (flip_small.mpr hz), Prod.mk.injEq, Fin.mk.injEq]
      exact ⟨orderSign_swap (base_ne z), by change z.neg.card + z.pos.card - 1 = _; dsimp [size]; omega⟩
    · simp only [label, dif_neg hz, dif_neg (fun h => hz (flip_small.mp h)),
        Prod.mk.injEq, Fin.mk.injEq]
      exact ⟨orderSign_swap (vectors_ne z hz),
        by change _ + (R (X z.neg) + R (X z.pos) - 1) = _; dsimp [score]; omega⟩
  have consistent (a b : Signed d) (ab : a.Included b) (mag : (label a).2 = (label b).2) :
      (label a).1 = (label b).1 := by
    have ap : a.pos ⊆ b.pos := ab.1
    have an : a.neg ⊆ b.neg := ab.2
    have cp := Finset.card_le_card ap
    have cn := Finset.card_le_card an
    have val := congrArg Fin.val mag
    by_cases ha : small a <;> by_cases hb : small b
    · simp only [label,dif_pos ha,dif_pos hb] at val ⊢
      have pa := size_pos a
      have pb := size_pos b
      have peq : a.pos = b.pos := Finset.eq_of_subset_of_card_le ap (by dsimp [size] at *; omega)
      have neq : a.neg = b.neg := Finset.eq_of_subset_of_card_le an (by dsimp [size] at *; omega)
      rw [peq,neq]
    · simp only [label,dif_pos ha,dif_neg hb] at val
      have ca := size_cap a ha
      have pa := size_pos a
      omega
    · exact False.elim (ha ⟨lt_of_le_of_lt cp hb.1,lt_of_le_of_lt cn hb.2⟩)
    · simp only [label,dif_neg ha,dif_neg hb] at val ⊢
      have xp := keyIndices_mono key ap
      have xn := keyIndices_mono key an
      have lp : R (X a.pos) ≤ R (X b.pos) := fallRank_mono xp
      have ln : R (X a.neg) ≤ R (X b.neg) := fallRank_mono xn
      have pa := high a ha
      have pb := high b hb
      have sep : R (X a.pos) = R (X b.pos) := by dsimp [score] at *; omega
      have sen : R (X a.neg) = R (X b.neg) := by dsimp [score] at *; omega
      rw [fallRank_stable bound dec xp sep,fallRank_stable bound dec xn sen]
  have dh := signed_tucker label anti consistent
  dsimp [m] at dh
  omega


open PEqualNP.NotBracket (notCount)

set_option maxHeartbeats 600000 in
lemma solve {d k n : ℕ} (key : Fin n ≃ Key d k) (hk : 0 < k) (hd : 2*k ≤ d)
    (hmax : d < 3*k) :
    (∀ g, Fits (KeyGraph key) g → Runs g 2 Finset.univ ∧
      ∀ C, Computes C g → 2 ≤ notCount C) ∧
    (∃ g, Fits (KeyGraph key) g ∧ ¬ Runs g 3 Finset.univ ∧ ∃ C, Computes C g ∧
      notCount C = 2 ∧ C.size - 2 ≤ d*2^d + 5*n) ∧
    (∃ g, Fits (KeyGraph key) g ∧ Decreasing g ∧ ¬ Runs g (d-2*k+3) Finset.univ) ∧
    ∀ g, Fits (KeyGraph key) g → Decreasing g →
      (∀ h, ¬ Runs g (h+1) Finset.univ → d+4 ≤ 2*k+2*h) ∧
      ∀ C, Computes C g → d+4 < 2*k+2^(notCount C + 1) := by
  have edge := graph_edge key hd
  refine ⟨?_,?_,?_,?_⟩
  · intro g hg
    have two := forced_two hg edge
    refine ⟨two,?_⟩
    intro C hc
    have hi := circuit_runs_bound hc 2 _ two
    by_contra no
    have cases : notCount C = 0 ∨ notCount C = 1 := by omega
    rcases cases with e | e <;> simp [e] at hi
  · refine ⟨twoAnswer (KeyGraph key),twoAnswer_fits _ (fun i l j => graph_no_triangle key hmax),
      twoAnswer_runs _,?_⟩
    obtain ⟨C,basis,rb,out,⟨tap,htap⟩,cnt,cost⟩ := circuit_upper (fun i => (key i).val)
    refine ⟨C,⟨basis,rb,out,tap,?_⟩,cnt,cost⟩
    intro x j
    refine (htap x j).trans ?_
    apply Bool.eq_iff_iff.mpr
    simp [twoAnswer_spec,KeyGraph]
  · let c : Fin n → ℕ := fun i => color (d-2*k+1) (key i).val
    exact ⟨byColor c,byColor_complete _ c (d-2*k+1)
      (fun i j => color_proper hk hd (key i).property (key j).property) (fun i => color_le _ _)⟩
  · intro g hg dec
    have lower : ∀ h, ¬ Runs g (h+1) Finset.univ → d+4 ≤ 2*k+2*h :=
      fun _ => decreasing_bound key hk hd hg dec
    refine ⟨lower,?_⟩
    intro C hc
    let p := 2^(notCount C)
    have pos : 0 < p := Nat.pow_pos (by decide)
    have hp : ¬ Runs g (p-1+1) Finset.univ := by
      intro r
      have b := circuit_runs_bound hc _ _ r
      change p-1+1 < p at b
      omega
    have b := lower (p-1) hp
    rw [Nat.pow_succ]
    change d+4 < 2*k+p*2
    omega

end PEqualNP.Outside.L_lib_1266_aux

theorem PEqualNP.Outside.L_lib_1266 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (k d : Nat), 0 < k → 2*k ≤ d → d < 3*k →
  let V := {a : Finset (Fin d) // a.card = k}
  let n := Fintype.card V
  let key := (Fintype.equivFin V).symm
  let H := fun (i j : Fin n) => Disjoint (key i).val (key j).val
  let fits := fun (g : Finset (Fin n) → Fin n → Bool) =>
    (∀ x j, (∀ i ∈ x, H i j) → g x j = true) ∧ (∀ x j, j ∈ x → g x j = false)
  let dec := fun (g : Finset (Fin n) → Fin n → Bool) =>
    ∀ x y, x ⊆ y → ∀ j, g y j = true → g x j = true
  let runs := fun (g : Finset (Fin n) → Fin n → Bool) =>
    Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun _ prev x => ∃ u v j, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ g u j = true ∧ g v j = false)
  let computes := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : Finset (Fin n) → Fin n → Bool) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ ∃ tap : Fin n → Fin (n+2+C.size),
      ∀ x j, let input := List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
             (C.wires input).getD (tap j).val false = g x j
  (∀ g, fits g → runs g 2 Finset.univ ∧
    ∀ C, computes C g → 2 ≤ PEqualNP.NotBracket.notCount C) ∧
  (∃ g, fits g ∧ ¬ runs g 3 Finset.univ ∧ ∃ C, computes C g ∧
    PEqualNP.NotBracket.notCount C = 2 ∧ C.size - 2 ≤ d*2^d + 5*n) ∧
  (∃ g, fits g ∧ dec g ∧ ¬ runs g (d-2*k+3) Finset.univ) ∧
  ∀ g, fits g → dec g →
    (∀ h, ¬ runs g (h+1) Finset.univ → d+4 ≤ 2*k+2*h) ∧
    ∀ C, computes C g → d+4 < 2*k + 2^(PEqualNP.NotBracket.notCount C + 1)) := by
  intro k d hk hd hmax
  dsimp only
  let key := (
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    (Fintype.equivFin {a : Finset (Fin d) // a.card = k}).symm)
  exact PEqualNP.Outside.L_lib_1266_aux.solve key hk hd hmax
