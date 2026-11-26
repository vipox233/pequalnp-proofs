import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20833_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g rest ih =>
    simp only [wiresFrom, List.foldl_cons] at ih ⊢
    rw [ih]
    simp; omega

lemma getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp [List.getD]
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · simp [List.getD, List.getElem?_append_left h]
    · have h1 : (V ++ [e]).length ≤ i := by simp; omega
      have h2 : V.length ≤ i := by omega
      simp [List.getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]

def inp (m : ℕ) (S : Finset ℕ) : List Bool :=
  List.ofFn fun i : Fin m => decide ((i : ℕ) ∈ S)

lemma inp_length (m : ℕ) (S : Finset ℕ) : (inp m S).length = m := by
  simp [inp]

lemma inp_getD (m : ℕ) (S : Finset ℕ) (i : ℕ) :
    (inp m S).getD i false = decide (i < m ∧ i ∈ S) := by
  by_cases hi : i < m
  · simp [inp, List.getD, hi]
  · have hlen : (inp m S).length ≤ i := by simp [inp]; omega
    simp [List.getD, List.getElem?_eq_none hlen, hi]

lemma oneEach_eq_inp {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i hi1 hi2
    have hi : i < n + m := by simpa [inp] using hi2
    simp only [oneEach, inp, List.getElem_append, List.length_ofFn, List.getElem_ofFn,
      Finset.mem_insert, Finset.mem_singleton]
    split_ifs with hlt
    · simp only [decide_eq_decide]
      constructor
      · intro h; left; exact congrArg Fin.val h
      · rintro (h | h)
        · exact Fin.ext h
        · omega
    · simp only [decide_eq_decide]
      constructor
      · intro h; right; have := congrArg Fin.val h; dsimp at this; omega
      · rintro (h | h)
        · have := u.isLt; omega
        · exact Fin.ext (by dsimp; omega)

lemma mono_eval (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ x y : List Bool, x.length = y.length →
      (∀ i, x.getD i false = true → y.getD i false = true) →
      ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs with
  | nil => intro x y _ hxy; exact hxy
  | cons g rest ih =>
    intro x y hlen hxy
    have hg := hmono g (List.mem_cons_self ..)
    have hrest : ∀ g' ∈ rest, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')
    simp only [wiresFrom, List.foldl_cons] at ih ⊢
    apply ih hrest _ _ (by simp [hlen])
    intro i hi
    rw [getD_snoc] at hi ⊢
    rw [hlen] at hi
    split_ifs at hi ⊢ with heq
    · rcases hg with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
        rintro b ⟨j, hj, rfl⟩
        exact hxy j (hi _ ⟨j, hj, rfl⟩)
      · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
        obtain ⟨_, ⟨j, hj, rfl⟩, hjv⟩ := hi
        exact ⟨_, ⟨j, hj, rfl⟩, hxy j hjv⟩
    · exact hxy i hi

lemma needed (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ N : Finset ℕ, ∃ N' : Finset ℕ, N'.card ≤ N.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ N', x.getD i false = y.getD i false) →
        ∀ i ∈ N, (wiresFrom gs x).getD i false = (wiresFrom gs y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro N
    exact ⟨N, by simp, fun x y _ _ h i hi => h i hi⟩
  | append_singleton gs g ih =>
    intro N
    have hgs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have hglen : g.inputs.length ≤ 2 := hg g (by simp)
    let idx := n + gs.length
    by_cases hidx : idx ∈ N
    · let N1 := (N.erase idx) ∪ g.inputs.toFinset
      obtain ⟨N', hcard, hdep⟩ := ih hgs N1
      have hN1card : N1.card ≤ N.card + 1 := by
        have h1 : N1.card ≤ (N.erase idx).card + g.inputs.toFinset.card := Finset.card_union_le _ _
        have h2 : (N.erase idx).card + 1 = N.card := by
          rw [Finset.card_erase_of_mem hidx]
          have := Finset.card_pos.mpr ⟨idx, hidx⟩; omega
        have h3 : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le _
        omega
      refine ⟨N', by simp; omega, ?_⟩
      intro x y hx hy hxy i hi
      rw [wiresFrom_append, wiresFrom_append]
      change (wiresFrom gs x ++ [g.op.eval (g.inputs.map fun j => (wiresFrom gs x).getD j false)]).getD i false =
             (wiresFrom gs y ++ [g.op.eval (g.inputs.map fun j => (wiresFrom gs y).getD j false)]).getD i false
      rw [getD_snoc, getD_snoc, wiresFrom_length, wiresFrom_length, hx, hy]
      split_ifs with heq
      · congr 1
        apply List.map_congr_left
        intro j hj
        exact hdep x y hx hy hxy j (Finset.mem_union_right _ (List.mem_toFinset.mpr hj))
      · exact hdep x y hx hy hxy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hi⟩))
    · obtain ⟨N', hcard, hdep⟩ := ih hgs N
      refine ⟨N', by simp; omega, ?_⟩
      intro x y hx hy hxy i hi
      rw [wiresFrom_append, wiresFrom_append]
      change (wiresFrom gs x ++ [g.op.eval (g.inputs.map fun j => (wiresFrom gs x).getD j false)]).getD i false =
             (wiresFrom gs y ++ [g.op.eval (g.inputs.map fun j => (wiresFrom gs y).getD j false)]).getD i false
      rw [getD_snoc, getD_snoc, wiresFrom_length, wiresFrom_length, hx, hy]
      have hne : i ≠ n + gs.length := fun h => hidx (by change n + gs.length ∈ N; rwa [← h])
      simp only [hne, ↓reduceIte]
      exact hdep x y hx hy hxy i hi

def forcedL {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v : Fin m, A u v = true ∧ ∃ u' : Fin n, A u' v = false

def forcedR {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u : Fin n, A u v = true ∧ ∃ v' : Fin m, A u v' = false

def forcedWires {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset ℕ :=
  (forcedL A).image (fun u : Fin n => (u : ℕ)) ∪
  (forcedR A).image (fun v : Fin m => n + (v : ℕ))

lemma card_forcedWires {n m : ℕ} (A : Fin n → Fin m → Bool) :
    (forcedWires A).card = (forcedL A).card + (forcedR A).card := by
  unfold forcedWires
  have hdis : Disjoint ((forcedL A).image (fun u : Fin n => (u : ℕ)))
      ((forcedR A).image (fun v : Fin m => n + (v : ℕ))) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp h2
    have := u.isLt; omega
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]

lemma forced_subset_of_dep {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit)
    (hmono : Monotone2 C) (hrep : Represents A C) (S : Finset ℕ)
    (hdep : ∀ x y : List Bool, x.length = n + m → y.length = n + m →
      (∀ i ∈ S, x.getD i false = y.getD i false) →
      (wiresFrom C.gates x).getD C.output false = (wiresFrom C.gates y).getD C.output false) :
    forcedWires A ⊆ S := by
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    have h := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact h
  have hev : ∀ x, C.eval x = (wiresFrom C.gates x).getD C.output false := fun _ => rfl
  have hA : ∀ (u : Fin n) (v : Fin m), C.eval (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v; rw [← oneEach_eq_inp]; exact hrep u v
  have hmon : ∀ P Q : Finset ℕ, P ⊆ Q → C.eval (inp (n + m) P) = true → C.eval (inp (n + m) Q) = true := by
    intro P Q hPQ hP
    rw [hev] at hP ⊢
    refine mono_eval C.gates hop _ _ (by simp [inp]) (fun i hi => ?_) C.output hP
    rw [inp_getD] at hi ⊢
    simp only [decide_eq_true_eq] at hi ⊢
    exact ⟨hi.1, hPQ hi.2⟩
  have hoff : ∀ (P : Finset ℕ) (w : ℕ), w ∉ S → C.eval (inp (n + m) (P.erase w)) = C.eval (inp (n + m) P) := by
    intro P w hw
    rw [hev, hev]
    refine hdep _ _ (inp_length _ _) (inp_length _ _) (fun i hi => ?_)
    rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
    have hne : i ≠ w := fun h => hw (h ▸ hi)
    tauto
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.mp hu).2
    by_contra hns
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hns
    rw [hA, h1] at e
    have hle := hmon _ {(u' : ℕ), n + (v : ℕ)} (fun z hz => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      tauto) e
    rw [hA, h2] at hle
    exact Bool.noConfusion hle
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨u, h1, v', h2⟩ := (Finset.mem_filter.mp hv).2
    by_contra hns
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hns
    rw [hA, h1] at e
    have hle := hmon _ {(u : ℕ), n + (v' : ℕ)} (fun z hz => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      tauto) e
    rw [hA, h2] at hle
    exact Bool.noConfusion hle

lemma reads_le {n m : ℕ} (A : Fin n → Fin m → Bool) {s : ℕ} (h : RepSizeAtMost A s) :
    (forcedL A).card + (forcedR A).card ≤ s + 1 := by
  obtain ⟨C, hmono, hsz, hrep⟩ := h
  obtain ⟨S, hcard, hdep⟩ := needed (n + m) C.gates (fun g hg => (hmono g hg).2) {C.output}
  have hsub := forced_subset_of_dep A C hmono hrep S (fun x y hx hy hxy => hdep x y hx hy hxy C.output (Finset.mem_singleton_self _))
  have hcc := Finset.card_le_card hsub
  rw [card_forcedWires] at hcc
  rw [Finset.card_singleton] at hcard
  have : C.gates.length ≤ s := hsz
  omega

end PEqualNP.Outside.L_meta_20833_aux

namespace PEqualNP.Outside.L_meta_20833_aux
def upperC : PEqualNP.CircuitLowerBounds.Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 17] }], output := 18 }
lemma upper_mono : PEqualNP.MetaComplexity.Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_20833_aux

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_20833 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30280803 : ℕ).testBit (5 * u.val + v.val)) 9 ∧ ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30280803 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  constructor
  · exact ⟨PEqualNP.Outside.L_meta_20833_aux.upperC, PEqualNP.Outside.L_meta_20833_aux.upper_mono, by decide, by decide +kernel⟩
  · intro h
    have hc := PEqualNP.Outside.L_meta_20833_aux.reads_le _ h
    revert hc
    decide +kernel
