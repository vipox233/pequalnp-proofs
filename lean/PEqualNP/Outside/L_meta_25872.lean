import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25872

def step (w : List Bool) (g : PEqualNP.MetaComplexity.BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

lemma getD_append_left (l1 l2 : List Bool) (u : ℕ) (h : u < l1.length) :
    (l1 ++ l2).getD u false = l1.getD u false := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right (l1 l2 : List Bool) (u : ℕ) (h : l1.length ≤ u) :
    (l1 ++ l2).getD u false = l2.getD (u - l1.length) false := by
  simp [List.getD, List.getElem?_append_right h]

lemma getD_eq_false_of_le (l : List Bool) (u : ℕ) (h : l.length ≤ u) :
    l.getD u false = false := by
  simp [List.getD, List.getElem?_eq_none h]

lemma getD_replicate_false (k u : ℕ) :
    (List.replicate k false).getD u false = false := by
  by_cases h : u < k
  · have hlen : u < (List.replicate k false).length := by simpa using h
    simp [List.getD, List.getElem?_eq_getElem hlen]
  · have hlen : (List.replicate k false).length ≤ u := by simp; omega
    exact getD_eq_false_of_le _ _ hlen

lemma getD_one (k : ℕ) (label : Fin k) (u : ℕ) (h : u < k) :
    (List.ofFn (fun v : Fin k => decide (v = label))).getD u false = decide (u = label.val) := by
  simp [List.getD, h, Fin.ext_iff]

lemma foldl_length (gs : List PEqualNP.MetaComplexity.BinaryGate) (x : List Bool) :
    (gs.foldl step x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g tl ih =>
    simp only [List.foldl, List.length_cons]
    rw [ih]
    simp [step]
    omega

lemma foldl_getD_lt (gs : List PEqualNP.MetaComplexity.BinaryGate) (x : List Bool) (u : ℕ)
    (hu : u < x.length) :
    (gs.foldl step x).getD u false = x.getD u false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g tl ih =>
    simp only [List.foldl]
    have hu' : u < (step x g).length := by
      simp [step]
      omega
    rw [ih (step x g) hu']
    exact getD_append_left x _ u hu

lemma foldl_getD_gate (gs : List PEqualNP.MetaComplexity.BinaryGate) (x : List Bool)
    (k : ℕ) (hk : k < gs.length)
    (hl : (gs.get ⟨k, hk⟩).left < x.length + k)
    (hr : (gs.get ⟨k, hk⟩).right < x.length + k) :
    (gs.foldl step x).getD (x.length + k) false =
      (gs.get ⟨k, hk⟩).op
        ((gs.foldl step x).getD (gs.get ⟨k, hk⟩).left false)
        ((gs.foldl step x).getD (gs.get ⟨k, hk⟩).right false) := by
  induction gs generalizing x k with
  | nil => cases hk
  | cons g tl ih =>
    cases k with
    | zero =>
      simp only [List.foldl, Nat.add_zero, List.get_eq_getElem, List.getElem_cons_zero] at hl hr ⊢
      have hlen : x.length < (step x g).length := by simp [step]
      rw [foldl_getD_lt tl (step x g) x.length hlen]
      rw [foldl_getD_lt tl (step x g) g.left (by simp [step]; omega)]
      rw [foldl_getD_lt tl (step x g) g.right (by simp [step]; omega)]
      simp only [step]
      rw [getD_append_left x _ g.left hl, getD_append_left x _ g.right hr]
      rw [getD_append_right x _ x.length (Nat.le_refl _)]
      simp
    | succ k' =>
      have hk' : k' < tl.length := by
        simp only [List.length_cons] at hk
        omega
      have hlen : (step x g).length = x.length + 1 := by simp [step]
      have hidx : x.length + (k' + 1) = (step x g).length + k' := by omega
      have hget : (g :: tl).get ⟨k' + 1, hk⟩ = tl.get ⟨k', hk'⟩ := rfl
      rw [hget] at hl hr ⊢
      simp only [List.foldl]
      rw [hidx]
      exact ih (step x g) k' hk' (by omega) (by omega)

lemma wires_getD_input (D : PEqualNP.MetaComplexity.BinaryCircuit) (x : List Bool)
    (raw w : ℕ) (hx : x.length = raw) (hw : w < raw) :
    (D.wires x).getD w false = x.getD w false := by
  exact foldl_getD_lt D.gates x w (by omega)

lemma wires_getD_gate (D : PEqualNP.MetaComplexity.BinaryCircuit) (x : List Bool)
    (raw g : ℕ) (hx : x.length = raw) (hg : g < D.gates.length)
    (hl : (D.gates.get ⟨g, hg⟩).left < raw + g)
    (hr : (D.gates.get ⟨g, hg⟩).right < raw + g) :
    (D.wires x).getD (raw + g) false =
      (D.gates.get ⟨g, hg⟩).op
        ((D.wires x).getD (D.gates.get ⟨g, hg⟩).left false)
        ((D.wires x).getD (D.gates.get ⟨g, hg⟩).right false) := by
  have h := foldl_getD_gate D.gates x g hg (by omega) (by omega)
  rw [hx] at h
  exact h

lemma wires_getD_ge (D : PEqualNP.MetaComplexity.BinaryCircuit) (x : List Bool)
    (raw w : ℕ) (hx : x.length = raw) (hw : raw + D.gates.length ≤ w) :
    (D.wires x).getD w false = false := by
  apply getD_eq_false_of_le
  have hlen : (D.wires x).length = x.length + D.gates.length :=
    foldl_length D.gates x
  omega

lemma bool_xor_factor (f : Bool → Bool) (a b : Bool) :
    (f a != f b) = ((f true != f false) && (a != b)) := by
  cases a <;> cases b <;> cases f false <;> cases f true <;> rfl

def regEval (D : PEqualNP.MetaComplexity.BinaryCircuit) (raw : ℕ)
    (sources entry : Finset ℕ) (src : ℕ → Bool) (ent : ↥entry → Bool) (w : ℕ) : Bool :=
  if w ∈ sources then src w
  else if he : w ∈ entry then ent ⟨w, he⟩
  else if h : raw ≤ w ∧ w - raw < D.gates.length then
    let node := D.gates.get ⟨w - raw, h.2⟩
    if _hl : node.left < w then
      if _hr : node.right < w then
        node.op (regEval D raw sources entry src ent node.left)
                (regEval D raw sources entry src ent node.right)
      else false
    else false
  else false
termination_by w

def extEval (D : PEqualNP.MetaComplexity.BinaryCircuit) (raw top : ℕ)
    (xbase : List Bool) (b : Bool) (w : ℕ) : Bool :=
  if w = raw + top then b
  else if w < raw then xbase.getD w false
  else if h : raw ≤ w ∧ w - raw < D.gates.length then
    let node := D.gates.get ⟨w - raw, h.2⟩
    if _hl : node.left < w then
      if _hr : node.right < w then
        node.op (extEval D raw top xbase b node.left)
                (extEval D raw top xbase b node.right)
      else false
    else false
  else false
termination_by w

lemma wires_eq_before_top (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (raw top : ℕ) (sources region entry : Finset ℕ)
    (hreg : region ⊆ Finset.range D.size)
    (htop : top ∈ region)
    (hgates : ∀ g : Fin D.gates.length,
      let node := D.gates.get g
      ∀ w ∈ ({node.left, node.right} : Finset ℕ),
        w < raw + g.val ∧
        (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) ∧
        (g.val ∉ region → w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)))
    (x y : List Bool) (hx : x.length = raw) (hy : y.length = raw)
    (hagree : ∀ u < raw, u ∉ sources → x.getD u false = y.getD u false)
    (w : ℕ) (hlt : w < raw + top) (hns : w ∉ sources) (hni : ¬(raw ≤ w ∧ w - raw ∈ region)) :
    (D.wires x).getD w false = (D.wires y).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwr : w < raw
    · rw [wires_getD_input D x raw w hx hwr, wires_getD_input D y raw w hy hwr]
      exact hagree w hwr hns
    · have htop_lt : top < D.gates.length := Finset.mem_range.mp (hreg htop)
      have hge : raw ≤ w := by omega
      have hglen : w - raw < D.gates.length := by omega
      have hnr : w - raw ∉ region := fun hr => hni ⟨hge, hr⟩
      let g : Fin D.gates.length := ⟨w - raw, hglen⟩
      have hgl := hgates g (D.gates.get g).left (Finset.mem_insert_self _ _)
      have hgr := hgates g (D.gates.get g).right (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      have hleft_lt : (D.gates.get g).left < w := by
        have := hgl.1
        change (D.gates.get g).left < raw + (w - raw) at this
        omega
      have hright_lt : (D.gates.get g).right < w := by
        have := hgr.1
        change (D.gates.get g).right < raw + (w - raw) at this
        omega
      have hleft_out := hgl.2.2 hnr
      have hright_out := hgr.2.2 hnr
      have hw_eq : raw + (w - raw) = w := by omega
      have hl_eq := ih (D.gates.get g).left hleft_lt (by omega) hleft_out.1
        (fun hin => by have := hleft_out.2 hin; omega)
      have hr_eq := ih (D.gates.get g).right hright_lt (by omega) hright_out.1
        (fun hin => by have := hright_out.2 hin; omega)
      have hgx := wires_getD_gate D x raw (w - raw) hx hglen hgl.1 hgr.1
      have hgy := wires_getD_gate D y raw (w - raw) hy hglen hgl.1 hgr.1
      rw [hw_eq] at hgx hgy
      rw [hgx, hgy]
      exact congrArg₂ (D.gates.get g).op hl_eq hr_eq

lemma wires_eq_regEval (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (raw top : ℕ) (sources region entry : Finset ℕ)
    (hsources_lt : ∀ s ∈ sources, s < raw)
    (hreg : region ⊆ Finset.range D.size)
    (hgates : ∀ g : Fin D.gates.length,
      let node := D.gates.get g
      ∀ w ∈ ({node.left, node.right} : Finset ℕ),
        w < raw + g.val ∧
        (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) ∧
        (g.val ∉ region → w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)))
    (x : List Bool) (hx : x.length = raw)
    (src : ℕ → Bool) (ent : ↥entry → Bool)
    (hsrc : ∀ s ∈ sources, x.getD s false = src s)
    (hent : ∀ e : ↥entry, (D.wires x).getD e.val false = ent e)
    (w : ℕ) (hw : w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) :
    (D.wires x).getD w false = regEval D raw sources entry src ent w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [regEval]
    by_cases hws : w ∈ sources
    · simp only [hws, ↓reduceIte]
      rw [wires_getD_input D x raw w hx (hsources_lt w hws)]
      exact hsrc w hws
    · by_cases hwe : w ∈ entry
      · simp only [hws, hwe, ↓reduceIte]
        exact hent ⟨w, hwe⟩
      · simp only [hws, hwe, ↓reduceIte]
        have hin : raw ≤ w ∧ w - raw ∈ region := by
          rcases hw with h1 | h2 | h3
          · exact absurd h1 hws
          · exact h2
          · exact absurd h3 hwe
        have hglen : w - raw < D.gates.length := Finset.mem_range.mp (hreg hin.2)
        have hcond : raw ≤ w ∧ w - raw < D.gates.length := ⟨hin.1, hglen⟩
        simp only [hcond, ↓reduceDIte]
        let g : Fin D.gates.length := ⟨w - raw, hglen⟩
        have hgl := hgates g (D.gates.get g).left (Finset.mem_insert_self _ _)
        have hgr := hgates g (D.gates.get g).right (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        have hw_eq : raw + (w - raw) = w := by omega
        have hl_lt : (D.gates.get g).left < w := by
          have := hgl.1
          change (D.gates.get g).left < raw + (w - raw) at this
          omega
        have hr_lt : (D.gates.get g).right < w := by
          have := hgr.1
          change (D.gates.get g).right < raw + (w - raw) at this
          omega
        simp only [g, hl_lt, hr_lt, ↓reduceDIte]
        have hl_eq := ih (D.gates.get g).left hl_lt (hgl.2.1 hin.2)
        have hr_eq := ih (D.gates.get g).right hr_lt (hgr.2.1 hin.2)
        have hgate := wires_getD_gate D x raw (w - raw) hx hglen hgl.1 hgr.1
        rw [hw_eq] at hgate
        rw [hgate]
        exact congrArg₂ (D.gates.get g).op hl_eq hr_eq

lemma wires_eq_extEval (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (raw top : ℕ) (sources region entry : Finset ℕ)
    (hgates : ∀ g : Fin D.gates.length,
      let node := D.gates.get g
      ∀ w ∈ ({node.left, node.right} : Finset ℕ),
        w < raw + g.val ∧
        (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) ∧
        (g.val ∉ region → w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)))
    (x xbase : List Bool) (hx : x.length = raw)
    (hagree : ∀ u < raw, u ∉ sources → x.getD u false = xbase.getD u false)
    (w : ℕ) (hns : w ∉ sources) (hin : (raw ≤ w ∧ w - raw ∈ region) → w = raw + top) :
    (D.wires x).getD w false =
      extEval D raw top xbase ((D.wires x).getD (raw + top) false) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [extEval]
    by_cases ht : w = raw + top
    · simp [ht]
    · by_cases hwr : w < raw
      · simp only [ht, hwr, ↓reduceIte]
        rw [wires_getD_input D x raw w hx hwr]
        exact hagree w hwr hns
      · by_cases hcond : raw ≤ w ∧ w - raw < D.gates.length
        · simp only [ht, hwr, hcond, ↓reduceIte, ↓reduceDIte]
          have hnr : w - raw ∉ region := fun hr => ht (hin ⟨hcond.1, hr⟩)
          let g : Fin D.gates.length := ⟨w - raw, hcond.2⟩
          have hgl := hgates g (D.gates.get g).left (Finset.mem_insert_self _ _)
          have hgr := hgates g (D.gates.get g).right (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
          have hw_eq : raw + (w - raw) = w := by omega
          have hl_lt : (D.gates.get g).left < w := by
            have := hgl.1
            change (D.gates.get g).left < raw + (w - raw) at this
            omega
          have hr_lt : (D.gates.get g).right < w := by
            have := hgr.1
            change (D.gates.get g).right < raw + (w - raw) at this
            omega
          simp only [g, hl_lt, hr_lt, ↓reduceDIte]
          have hlo := hgl.2.2 hnr
          have hro := hgr.2.2 hnr
          have hl_eq := ih (D.gates.get g).left hl_lt hlo.1 hlo.2
          have hr_eq := ih (D.gates.get g).right hr_lt hro.1 hro.2
          have hgate := wires_getD_gate D x raw (w - raw) hx hcond.2 hgl.1 hgr.1
          rw [hw_eq] at hgate
          rw [hgate]
          exact congrArg₂ (D.gates.get g).op hl_eq hr_eq
        · simp only [ht, hwr, hcond, ↓reduceIte, ↓reduceDIte]
          exact wires_getD_ge D x raw w hx (by omega)

lemma factor_bank (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (raw top : ℕ) (sources region entry : Finset ℕ)
    (hsources_lt : ∀ s ∈ sources, s < raw)
    (hreg : region ⊆ Finset.range D.size)
    (htop : top ∈ region)
    (hentry : ∀ e ∈ entry, e < raw + top ∧ e ∉ sources ∧ ¬(raw ≤ e ∧ e - raw ∈ region))
    (hgates : ∀ g : Fin D.gates.length,
      let node := D.gates.get g
      ∀ w ∈ ({node.left, node.right} : Finset ℕ),
        w < raw + g.val ∧
        (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ entry) ∧
        (g.val ∉ region → w ∉ sources ∧ ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)))
    (hout_ns : D.output ∉ sources)
    (hout_in : (raw ≤ D.output ∧ D.output - raw ∈ region) → D.output = raw + top)
    (x_on x_off : List Bool) (hon_len : x_on.length = raw) (hoff_len : x_off.length = raw)
    (target : ℕ)
    (hagree : ∀ u < raw, u ∉ sources → x_on.getD u false = x_off.getD u false)
    (hoff_src : ∀ s ∈ sources, x_off.getD s false = false)
    (hon_src : ∀ s ∈ sources, x_on.getD s false = decide (s = target)) :
    (D.eval x_on != D.eval x_off) =
      ((extEval D raw top x_off true D.output != extEval D raw top x_off false D.output) &&
       (regEval D raw sources entry (fun s => decide (s = target))
          (fun e => (D.wires x_off).getD e.val false) (raw + top) !=
        regEval D raw sources entry (fun _ => false)
          (fun e => (D.wires x_off).getD e.val false) (raw + top))) := by
  have heval_on : D.eval x_on =
      extEval D raw top x_off ((D.wires x_on).getD (raw + top) false) D.output :=
    wires_eq_extEval D raw top sources region entry hgates x_on x_off hon_len hagree
      D.output hout_ns hout_in
  have heval_off : D.eval x_off =
      extEval D raw top x_off ((D.wires x_off).getD (raw + top) false) D.output :=
    wires_eq_extEval D raw top sources region entry hgates x_off x_off hoff_len
      (fun _ _ _ => rfl) D.output hout_ns hout_in
  rw [heval_on, heval_off]
  rw [bool_xor_factor (fun b => extEval D raw top x_off b D.output)]
  have hent_on : ∀ e : ↥entry,
      (D.wires x_on).getD e.val false = (D.wires x_off).getD e.val false := by
    intro e
    have he := hentry e.val e.property
    exact wires_eq_before_top D raw top sources region entry hreg htop hgates
      x_on x_off hon_len hoff_len hagree e.val he.1 he.2.1 he.2.2
  have htop_in : raw + top ∈ sources ∨ (raw ≤ raw + top ∧ raw + top - raw ∈ region) ∨ raw + top ∈ entry :=
    Or.inr (Or.inl ⟨Nat.le_add_right raw top, by simpa using htop⟩)
  have htop_on : (D.wires x_on).getD (raw + top) false =
      regEval D raw sources entry (fun s => decide (s = target))
        (fun e => (D.wires x_off).getD e.val false) (raw + top) :=
    wires_eq_regEval D raw top sources region entry hsources_lt hreg hgates
      x_on hon_len (fun s => decide (s = target))
      (fun e => (D.wires x_off).getD e.val false) hon_src hent_on (raw + top) htop_in
  have htop_off : (D.wires x_off).getD (raw + top) false =
      regEval D raw sources entry (fun _ => false)
        (fun e => (D.wires x_off).getD e.val false) (raw + top) :=
    wires_eq_regEval D raw top sources region entry hsources_lt hreg hgates
      x_off hoff_len (fun _ => false)
      (fun e => (D.wires x_off).getD e.val false) hoff_src (fun _ => rfl) (raw + top) htop_in
  rw [htop_on, htop_off]

end PEqualNP.Outside.L_meta_25872

theorem PEqualNP.Outside.L_meta_25872 : ∀ (n m : ℕ) (D : PEqualNP.MetaComplexity.BinaryCircuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n+m
  let sources := R.image (fun i => i.val) ∪ B.image (fun j => n+j.val)
  let inside := fun w : ℕ => raw ≤ w ∧ w-raw ∈ region
  let one := fun (k : ℕ) (label : Fin k) => List.ofFn (fun v : Fin k => decide (v = label))
  let rowOff := fun j : Fin m => List.replicate n false ++ one m j
  let colOff := fun i : Fin n => one n i ++ List.replicate m false
  let value := fun (i : Fin n) (j : Fin m) => D.eval (one n i ++ one m j)
  region ⊆ Finset.range D.size → top ∈ region →
  (∀ e ∈ entry, e < raw+top ∧ e ∉ sources ∧ ¬inside e) →
  (∀ g : Fin D.gates.length,
    let node := D.gates.get g
    ∀ w ∈ ({node.left, node.right} : Finset ℕ),
      w < raw+g.val ∧
      (g.val ∈ region → w ∈ sources ∨ inside w ∨ w ∈ entry) ∧
      (g.val ∉ region → w ∉ sources ∧ (inside w → w = raw+top))) →
  D.output ∉ sources → (inside D.output → D.output = raw+top) →
    (∃ (mask : Fin m → Bool) (response : Fin n → (↥entry → Bool) → Bool),
      ∀ i ∈ R, ∀ j ∉ B,
        (value i j != D.eval (rowOff j)) =
        (mask j && response i (fun e => (D.wires (rowOff j)).getD e.val false))) ∧
    (∃ (mask : Fin n → Bool) (response : Fin m → (↥entry → Bool) → Bool),
      ∀ j ∈ B, ∀ i ∉ R,
        (value i j != D.eval (colOff i)) =
        (mask i && response j (fun e => (D.wires (colOff i)).getD e.val false))) := by
  intro n m D R B region entry top raw sources inside one rowOff colOff value
    hreg htop hentry hgates hout_ns hout_in
  have hsources_lt : ∀ s ∈ sources, s < raw := by
    intro s hs
    rcases Finset.mem_union.mp hs with hR | hB
    · rcases Finset.mem_image.mp hR with ⟨i, _, rfl⟩
      omega
    · rcases Finset.mem_image.mp hB with ⟨j, _, rfl⟩
      omega
  constructor
  · refine ⟨fun j =>
        PEqualNP.Outside.L_meta_25872.extEval D raw top (rowOff j) true D.output !=
        PEqualNP.Outside.L_meta_25872.extEval D raw top (rowOff j) false D.output,
      fun i ent =>
        PEqualNP.Outside.L_meta_25872.regEval D raw sources entry
          (fun s => decide (s = i.val)) ent (raw + top) !=
        PEqualNP.Outside.L_meta_25872.regEval D raw sources entry
          (fun _ => false) ent (raw + top),
      ?_⟩
    intro i hiR j hjB
    have hon_len : (one n i ++ one m j).length = raw := by
      simp [one, raw]
    have hoff_len : (rowOff j).length = raw := by
      simp [rowOff, one, raw]
    have hagree : ∀ u < raw, u ∉ sources →
        (one n i ++ one m j).getD u false = (rowOff j).getD u false := by
      intro u hu huns
      by_cases hun : u < n
      · have h1 : (one n i ++ one m j).getD u false = (one n i).getD u false :=
          PEqualNP.Outside.L_meta_25872.getD_append_left _ _ u (by simp [one, hun])
        have h2 : (rowOff j).getD u false = (List.replicate n false).getD u false :=
          PEqualNP.Outside.L_meta_25872.getD_append_left _ _ u (by simp [hun])
        rw [h1, h2, PEqualNP.Outside.L_meta_25872.getD_one n i u hun,
          PEqualNP.Outside.L_meta_25872.getD_replicate_false]
        have hne : u ≠ i.val := by
          intro heq
          apply huns
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiR, heq.symm⟩)
        simp [hne]
      · have hge : n ≤ u := by omega
        have h1 : (one n i ++ one m j).getD u false = (one m j).getD (u - n) false := by
          rw [PEqualNP.Outside.L_meta_25872.getD_append_right (one n i) (one m j) u (by simp [one, hge])]
          simp [one]
        have h2 : (rowOff j).getD u false = (one m j).getD (u - n) false := by
          rw [PEqualNP.Outside.L_meta_25872.getD_append_right (List.replicate n false) (one m j) u (by simp [hge])]
          simp
        rw [h1, h2]
    have hoff_src : ∀ s ∈ sources, (rowOff j).getD s false = false := by
      intro s hs
      rcases Finset.mem_union.mp hs with hR | hB
      · rcases Finset.mem_image.mp hR with ⟨i', _, rfl⟩
        rw [PEqualNP.Outside.L_meta_25872.getD_append_left _ _ i'.val (by simp)]
        exact PEqualNP.Outside.L_meta_25872.getD_replicate_false n i'.val
      · rcases Finset.mem_image.mp hB with ⟨j', hj'B, rfl⟩
        have h2 : (rowOff j).getD (n + j'.val) false = (one m j).getD j'.val false := by
          rw [PEqualNP.Outside.L_meta_25872.getD_append_right
            (List.replicate n false) (one m j) (n + j'.val) (by simp)]
          simp
        rw [h2, PEqualNP.Outside.L_meta_25872.getD_one m j j'.val j'.isLt]
        have hne : j'.val ≠ j.val := fun heq => hjB (Fin.ext heq ▸ hj'B)
        simp [hne]
    have hon_src : ∀ s ∈ sources, (one n i ++ one m j).getD s false = decide (s = i.val) := by
      intro s hs
      rcases Finset.mem_union.mp hs with hR | hB
      · rcases Finset.mem_image.mp hR with ⟨i', _, rfl⟩
        rw [PEqualNP.Outside.L_meta_25872.getD_append_left _ _ i'.val (by simp [one])]
        exact PEqualNP.Outside.L_meta_25872.getD_one n i i'.val i'.isLt
      · rcases Finset.mem_image.mp hB with ⟨j', hj'B, rfl⟩
        have h1 : (one n i ++ one m j).getD (n + j'.val) false = (one m j).getD j'.val false := by
          rw [PEqualNP.Outside.L_meta_25872.getD_append_right
            (one n i) (one m j) (n + j'.val) (by simp [one])]
          simp [one]
        rw [h1, PEqualNP.Outside.L_meta_25872.getD_one m j j'.val j'.isLt]
        have hne1 : j'.val ≠ j.val := fun heq => hjB (Fin.ext heq ▸ hj'B)
        have hne2 : n + j'.val ≠ i.val := by omega
        simp [hne1, hne2]
    exact PEqualNP.Outside.L_meta_25872.factor_bank D raw top sources region entry
      hsources_lt hreg htop hentry hgates hout_ns hout_in
      (one n i ++ one m j) (rowOff j) hon_len hoff_len i.val hagree hoff_src hon_src
  · refine ⟨fun i =>
        PEqualNP.Outside.L_meta_25872.extEval D raw top (colOff i) true D.output !=
        PEqualNP.Outside.L_meta_25872.extEval D raw top (colOff i) false D.output,
      fun j ent =>
        PEqualNP.Outside.L_meta_25872.regEval D raw sources entry
          (fun s => decide (s = n + j.val)) ent (raw + top) !=
        PEqualNP.Outside.L_meta_25872.regEval D raw sources entry
          (fun _ => false) ent (raw + top),
      ?_⟩
    intro j hjB i hiR
    have hon_len : (one n i ++ one m j).length = raw := by
      simp [one, raw]
    have hoff_len : (colOff i).length = raw := by
      simp [colOff, one, raw]
    have hagree : ∀ u < raw, u ∉ sources →
        (one n i ++ one m j).getD u false = (colOff i).getD u false := by
      intro u hu huns
      by_cases hun : u < n
      · have h1 : (one n i ++ one m j).getD u false = (one n i).getD u false :=
          PEqualNP.Outside.L_meta_25872.getD_append_left _ _ u (by simp [one, hun])
        have h2 : (colOff i).getD u false = (one n i).getD u false :=
          PEqualNP.Outside.L_meta_25872.getD_append_left _ _ u (by simp [one, hun])
        rw [h1, h2]
      · have hge : n ≤ u := by omega
        have hltm : u - n < m := by omega
        have h1 : (one n i ++ one m j).getD u false = (one m j).getD (u - n) false := by
          rw [PEqualNP.Outside.L_meta_25872.getD_append_right (one n i) (one m j) u (by simp [one, hge])]
          simp [one]
        have h2 : (colOff i).getD u false = (List.replicate m false).getD (u - n) false := by
          rw [PEqualNP.Outside.L_meta_25872.getD_append_right (one n i) (List.replicate m false) u (by simp [one, hge])]
          simp [one]
        rw [h1, h2, PEqualNP.Outside.L_meta_25872.getD_one m j (u - n) hltm,
          PEqualNP.Outside.L_meta_25872.getD_replicate_false]
        have hne : u - n ≠ j.val := by
          intro heq
          apply huns
          exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hjB, by omega⟩)
        simp [hne]
    have hoff_src : ∀ s ∈ sources, (colOff i).getD s false = false := by
      intro s hs
      rcases Finset.mem_union.mp hs with hR | hB
      · rcases Finset.mem_image.mp hR with ⟨i', hi'R, rfl⟩
        rw [PEqualNP.Outside.L_meta_25872.getD_append_left _ _ i'.val (by simp [one])]
        rw [PEqualNP.Outside.L_meta_25872.getD_one n i i'.val i'.isLt]
        have hne : i'.val ≠ i.val := fun heq => hiR (Fin.ext heq ▸ hi'R)
        simp [hne]
      · rcases Finset.mem_image.mp hB with ⟨j', _, rfl⟩
        have h2 : (colOff i).getD (n + j'.val) false = (List.replicate m false).getD j'.val false := by
          rw [PEqualNP.Outside.L_meta_25872.getD_append_right
            (one n i) (List.replicate m false) (n + j'.val) (by simp [one])]
          simp [one]
        rw [h2]
        exact PEqualNP.Outside.L_meta_25872.getD_replicate_false m j'.val
    have hon_src : ∀ s ∈ sources, (one n i ++ one m j).getD s false = decide (s = n + j.val) := by
      intro s hs
      rcases Finset.mem_union.mp hs with hR | hB
      · rcases Finset.mem_image.mp hR with ⟨i', hi'R, rfl⟩
        rw [PEqualNP.Outside.L_meta_25872.getD_append_left _ _ i'.val (by simp [one])]
        rw [PEqualNP.Outside.L_meta_25872.getD_one n i i'.val i'.isLt]
        have hne1 : i'.val ≠ i.val := fun heq => hiR (Fin.ext heq ▸ hi'R)
        have hne2 : i'.val ≠ n + j.val := by omega
        simp [hne1, hne2]
      · rcases Finset.mem_image.mp hB with ⟨j', _, rfl⟩
        have h1 : (one n i ++ one m j).getD (n + j'.val) false = (one m j).getD j'.val false := by
          rw [PEqualNP.Outside.L_meta_25872.getD_append_right
            (one n i) (one m j) (n + j'.val) (by simp [one])]
          simp [one]
        rw [h1, PEqualNP.Outside.L_meta_25872.getD_one m j j'.val j'.isLt]
        simp
    exact PEqualNP.Outside.L_meta_25872.factor_bank D raw top sources region entry
      hsources_lt hreg htop hentry hgates hout_ns hout_in
      (one n i ++ one m j) (colOff i) hon_len hoff_len (n + j.val) hagree hoff_src hon_src
