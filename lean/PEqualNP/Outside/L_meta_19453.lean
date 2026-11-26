import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19453

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

private def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wstep_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl wstep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

private lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) : (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD_left {n m : ℕ} (u : Fin n) (v : Fin m) (i : Fin n) :
    (oneEach u v).getD i.val false = decide (i = u) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

private lemma oneEach_getD_right {n m : ℕ} (u : Fin n) (v : Fin m) (j : Fin m) :
    (oneEach u v).getD (n + j.val) false = decide (j = v) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, j.isLt]

private lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

private lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

private lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

private lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

private lemma outsideLength (xs : List Bool) (i : ℕ) (h : xs.length ≤ i) :
    xs.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private lemma snocOther (xs : List Bool) (b : Bool) (i : ℕ) (h : i ≠ xs.length) :
    (xs ++ [b]).getD i false = xs.getD i false := by
  by_cases hi : i < xs.length
  · exact List.getD_append _ _ _ _ hi
  · rw [outsideLength _ _ (by simp; omega), outsideLength _ _ (by omega)]

lemma full (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit) (v v' : Fin m)
    (rep : Represents A C)
    (silent : ∀ z ∈ [v,v'], C.output ≠ n+z.val ∧ ∀ j < C.gates.length,
      (C.output = n+m+j ∨ (n+m ≤ C.output ∧ InCone (n+m) C j (C.output-(n+m)))) →
        n+z.val ∉ (C.gates.getD j ⟨GateOp.and, []⟩).inputs) (u : Fin n) :
    A u v = A u v' := by
  let N := n+m
  let W := fun (k : ℕ) (z : Fin m) => (C.gates.take k).foldl wstep (oneEach u z)
  let live := fun j => C.output = N+j ∨ (N ≤ C.output ∧ InCone N C j (C.output-N))
  let needed := fun w => (w < N ∧ w ≠ n+v.val ∧ w ≠ n+v'.val) ∨ (N ≤ w ∧ live (w-N))
  have wlen (k : ℕ) (z : Fin m) (h : k ≤ C.gates.length) : (W k z).length = N+k := by
    simp [W,foldl_wstep_len,oneEach_len,N,Nat.min_eq_left h]
  have eqs (k : ℕ) (hk : k ≤ C.gates.length) (w : ℕ) (hw : needed w) :
      (W k v).getD w false = (W k v').getD w false := by
    induction k generalizing w with
    | zero =>
      change (oneEach u v).getD w false = (oneEach u v').getD w false
      rcases hw with ⟨hb, hv, hv'⟩ | ⟨hb,_⟩
      · by_cases hl : w < n
        · exact (oneEach_getD_left u v ⟨w,hl⟩).trans (oneEach_getD_left u v' ⟨w,hl⟩).symm
        · let z : Fin m := ⟨w-n, by dsimp [N] at hb; omega⟩
          have hz : n+z.val=w := by dsimp [z]; omega
          have h1 : z ≠ v := fun h => hv (hz ▸ congrArg (fun x : Fin m => n+x.val) h)
          have h2 : z ≠ v' := fun h => hv' (hz ▸ congrArg (fun x : Fin m => n+x.val) h)
          rw [←hz, oneEach_getD_right, oneEach_getD_right]
          simp [h1,h2]
      · rw [outsideLength _ _ (by rw [oneEach_len]; exact hb),
            outsideLength _ _ (by rw [oneEach_len]; exact hb)]
    | succ k ih =>
      have hk' : k < C.gates.length := by omega
      let g := C.gates[k]
      have hg1 : C.gates.getD k ⟨GateOp.and,[]⟩ = g := by simp [g,List.getD_eq_getElem?_getD,hk']
      have hg2 : gateAt C k = g := by simp [gateAt,g,List.getD_eq_getElem?_getD,hk']
      have step (z : Fin m) : W (k+1) z = W k z ++ [g.op.eval (g.inputs.map fun i => (W k z).getD i false)] := by
        simp only [W,List.take_succ_eq_append_getElem hk',List.foldl_append,List.foldl_cons,List.foldl_nil,wstep,g]
      rw [step,step]
      by_cases he : w=N+k
      · subst w
        have hl : live k := by
          rcases hw with ⟨h,_,_⟩ | ⟨_,h⟩
          · omega
          · simpa using h
        have inputEq : ∀ i ∈ g.inputs, (W k v).getD i false = (W k v').getD i false := by
          intro i hi
          by_cases hp : i < N
          · apply ih (by omega) i (Or.inl ⟨hp,?_,?_⟩)
            · intro e
              exact (silent v (by simp)).2 k hk' hl (hg1 ▸ e ▸ hi)
            · intro e
              exact (silent v' (by simp)).2 k hk' hl (hg1 ▸ e ▸ hi)
          · by_cases hearly : i < N+k
            · have edge : InCone N C (i-N) k := by
                apply (inCone_iff _ _ _ _).2
                refine ⟨hk',i-N,by omega,?_,Or.inl rfl⟩
                rwa [hg2,show N+(i-N)=i by omega]
              apply ih (by omega) i (Or.inr ⟨by omega, Or.inr ?_⟩)
              rcases hl with hout | ⟨hout,con⟩
              · exact ⟨by omega, by simpa [hout] using edge⟩
              · exact ⟨hout,inCone_trans _ _ _ _ edge _ con⟩
            · rw [outsideLength _ _ (by rw [wlen k v (by omega)]; omega),
                  outsideLength _ _ (by rw [wlen k v' (by omega)]; omega)]
        have maps := List.map_congr_left inputEq
        rw [maps, List.getD_append_right _ _ _ _ (by rw [wlen k v (by omega)]),
            List.getD_append_right _ _ _ _ (by rw [wlen k v' (by omega)])]
        rw [wlen k v (by omega),wlen k v' (by omega)]
      · rw [snocOther _ _ _ (by rwa [wlen k v (by omega)]),snocOther _ _ _ (by rwa [wlen k v' (by omega)])]
        exact ih (by omega) w hw
  have hn : needed C.output := by
    by_cases h : C.output < N
    · exact Or.inl ⟨h,(silent v (by simp)).1,(silent v' (by simp)).1⟩
    · exact Or.inr ⟨by omega,Or.inl (by omega)⟩
  rw [← rep u v, ← rep u v']
  change (C.gates.foldl wstep (oneEach u v)).getD C.output false =
    (C.gates.foldl wstep (oneEach u v')).getD C.output false
  simpa only [W,List.take_length] using eqs C.gates.length le_rfl C.output hn

end PEqualNP.Outside.L_meta_19453

theorem PEqualNP.Outside.L_meta_19453 : (∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (v v' : Fin m), PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ (n + v.val) ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → (n + v.val) ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → (C.output ≠ (n + v'.val) ∧ ∀ g < C.gates.length, (C.output = n + m + g ∨ (n + m ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → (n + v'.val) ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∀ u : Fin n, A u v = A u v') := by
  intro n m A C v v' _ rep sv sv' u
  apply PEqualNP.Outside.L_meta_19453.full n m A C v v' rep _ u
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl
  · exact sv
  · exact sv'
