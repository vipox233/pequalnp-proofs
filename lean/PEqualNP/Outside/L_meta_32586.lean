import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32586

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev Legal (N : ℕ) (C : Circuit) : Prop :=
  ReadsBack (N + N) C ∧ C.output < N + N + C.size ∧
  ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
    (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresPrefix (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl wiresStep x

lemma wiresPrefix_nil (x : List Bool) : wiresPrefix [] x = x := rfl

lemma wiresPrefix_concat (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresPrefix (gs ++ [g]) x = wiresStep (wiresPrefix gs x) g := by
  simp [wiresPrefix, List.foldl_append]

lemma wiresPrefix_length (gs : List Gate) (x : List Bool) :
    (wiresPrefix gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresPrefix]
  | append_singleton gs g ih =>
    rw [wiresPrefix_concat, wiresStep, List.length_append, List.length_singleton, ih,
      List.length_append, List.length_singleton]
    omega

lemma getD_append_lt {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD]

lemma wiresPrefix_take_getD (gs : List Gate) (x : List Bool) (k w : ℕ)
    (hk : k ≤ gs.length) (hw : w < x.length + k) :
    (wiresPrefix gs x).getD w false = (wiresPrefix (gs.take k) x).getD w false := by
  induction gs using List.reverseRecOn generalizing k with
  | nil => simp at hk; subst hk; rfl
  | append_singleton gs g ih =>
    by_cases hle : k ≤ gs.length
    · rw [List.take_append_of_le_length hle, wiresPrefix_concat, wiresStep,
        getD_append_lt _ _ _ _ (by rw [wiresPrefix_length]; omega)]
      exact ih k hle hw
    · have hk_eq : k = gs.length + 1 := by simp at hk; omega
      subst hk_eq
      rw [List.take_of_length_le (by simp)]

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  have h := wiresPrefix_take_getD C.gates x 0 i (Nat.zero_le _) (by omega)
  change (wiresPrefix C.gates x).getD i false = x.getD i false
  simpa [wiresPrefix] using h

lemma wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ)
    (hRB : ReadsBack x.length C) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have h1 := wiresPrefix_take_getD C.gates x (j + 1) (x.length + j) (by omega) (by omega)
  have htake : C.gates.take (j + 1) = C.gates.take j ++ [C.gates[j]] := by
    rw [List.take_succ_eq_append_getElem hj]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD, hj]
  change (wiresPrefix C.gates x).getD (x.length + j) false = _
  rw [h1, htake, wiresPrefix_concat, wiresStep]
  have hlen : (wiresPrefix (C.gates.take j) x).length = x.length + j := by
    rw [wiresPrefix_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [← hlen, getD_append_eq, hgate]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < x.length + j := hRB j hj i (by rwa [hgate])
  exact (wiresPrefix_take_getD C.gates x j i (by omega) hi').symm

def isNot : GateOp → Bool
  | .not => true
  | _ => false

def frontierAux (n : ℕ) (C : Circuit) : ℕ → Finset ℕ × ℕ × Bool → Finset ℕ × ℕ × Bool
  | 0, st => st
  | k + 1, (F, e, hn) =>
    if n + k ∈ F then
      let g := gateAt C k
      frontierAux n C k ((F.erase (n + k)) ∪ g.inputs.toFinset, e + 1, hn || isNot g.op)
    else
      frontierAux n C k (F, e, hn)

lemma frontierAux_inv (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hG : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (m : ℕ) (hm : m ≤ C.gates.length) (F : Finset ℕ) (e : ℕ) (hn : Bool)
    (hF : ∀ w ∈ F, w < n + m)
    (hcard : F.card + (if hn then 1 else 0) ≤ e + 1) :
    let res := frontierAux n C m (F, e, hn)
    (∀ w ∈ res.1, w < n) ∧
    res.1.card + (if res.2.2 then 1 else 0) ≤ res.2.1 + 1 ∧
    res.2.1 ≤ e + m := by
  induction m generalizing F e hn with
  | zero =>
    simp only [frontierAux]
    refine ⟨by simpa using hF, hcard, by omega⟩
  | succ k ih =>
    by_cases hmem : n + k ∈ F
    · simp only [frontierAux, hmem, ↓reduceIte]
      have hk : k < C.gates.length := by omega
      have hg_mem : gateAt C k ∈ C.gates := by
        simp [gateAt, List.getD, hk]
      have hg := hG (gateAt C k) hg_mem
      have hF' : ∀ w ∈ (F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset, w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · have hwF := Finset.mem_of_mem_erase hw1
          have hne := Finset.ne_of_mem_erase hw1
          have := hF w hwF
          omega
        · exact hRB k hk w (List.mem_toFinset.mp hw2)
      have herase : (F.erase (n + k)).card + 1 = F.card := Finset.card_erase_add_one hmem
      have hunion : ((F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset).card ≤
          (F.erase (n + k)).card + (gateAt C k).inputs.toFinset.card := Finset.card_union_le _ _
      have htofin : (gateAt C k).inputs.toFinset.card ≤ (gateAt C k).inputs.length :=
        List.toFinset_card_le _
      have hcard' : ((F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset).card +
          (if hn || isNot (gateAt C k).op then 1 else 0) ≤ (e + 1) + 1 := by
        rcases hg.2 with hand | hor | ⟨hnot, hlen1⟩
        · simp only [hand, isNot, Bool.or_false]
          have := hg.1
          omega
        · simp only [hor, isNot, Bool.or_false]
          have := hg.1
          omega
        · simp only [hnot, isNot, Bool.or_true]
          cases hn <;> simp at hcard ⊢ <;> omega
      have hrec := ih (by omega) _ (e + 1) (hn || isNot (gateAt C k).op) hF' hcard'
      exact ⟨hrec.1, hrec.2.1, by omega⟩
    · simp only [frontierAux, hmem, ↓reduceIte]
      have hF' : ∀ w ∈ F, w < n + k := by
        intro w hw
        have hlt := hF w hw
        have hne : w ≠ n + k := fun heq => hmem (heq ▸ hw)
        omega
      have hrec := ih (by omega) F e hn hF' hcard
      exact ⟨hrec.1, hrec.2.1, by omega⟩

lemma frontierAux_agree (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (m : ℕ) (hm : m ≤ C.gates.length) (F : Finset ℕ) (e : ℕ) (hn : Bool)
    (hF : ∀ w ∈ F, w < n + m)
    (hagree : ∀ w ∈ (frontierAux n C m (F, e, hn)).1, x.getD w false = y.getD w false) :
    ∀ w ∈ F, (C.wires x).getD w false = (C.wires y).getD w false := by
  induction m generalizing F e hn with
  | zero =>
    intro w hw
    have hw_lt : w < n := by simpa using hF w hw
    rw [wires_getD_input C x w (by omega), wires_getD_input C y w (by omega)]
    exact hagree w hw
  | succ k ih =>
    simp only [frontierAux] at hagree
    split_ifs at hagree with hmem
    · have hk : k < C.gates.length := by omega
      have hF' : ∀ w ∈ (F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset, w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · have := hF w (Finset.mem_of_mem_erase hw1)
          have := Finset.ne_of_mem_erase hw1
          omega
        · exact hRB k hk w (List.mem_toFinset.mp hw2)
      have ih_res := ih (by omega) _ (e + 1) (hn || isNot (gateAt C k).op) hF' hagree
      intro w hw
      by_cases hwk : w = n + k
      · subst hwk
        have hgx := wires_getD_gate C x k (hx ▸ hRB) hk
        have hgy := wires_getD_gate C y k (hy ▸ hRB) hk
        rw [hx] at hgx; rw [hy] at hgy
        rw [hgx, hgy]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih_res i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
      · exact ih_res w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩))
    · have hF' : ∀ w ∈ F, w < n + k := by
        intro w hw
        have := hF w hw
        have hne : w ≠ n + k := fun heq => hmem (heq ▸ hw)
        omega
      exact ih (by omega) F e hn hF' hagree

lemma frontierAux_mono (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hG : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (m : ℕ) (hm : m ≤ C.gates.length) (F : Finset ℕ) (e : ℕ) (hn : Bool)
    (hF : ∀ w ∈ F, w < n + m)
    (hnoNot : (frontierAux n C m (F, e, hn)).2.2 = false)
    (hmono : ∀ w ∈ (frontierAux n C m (F, e, hn)).1,
      x.getD w false = true → y.getD w false = true) :
    ∀ w ∈ F, (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  induction m generalizing F e hn with
  | zero =>
    intro w hw hwx
    have hw_lt : w < n := by simpa using hF w hw
    rw [wires_getD_input C x w (by omega)] at hwx
    rw [wires_getD_input C y w (by omega)]
    exact hmono w hw hwx
  | succ k ih =>
    simp only [frontierAux] at hnoNot hmono
    split_ifs at hnoNot hmono with hmem
    · have hk : k < C.gates.length := by omega
      have hF' : ∀ w ∈ (F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset, w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · have := hF w (Finset.mem_of_mem_erase hw1)
          have := Finset.ne_of_mem_erase hw1
          omega
        · exact hRB k hk w (List.mem_toFinset.mp hw2)
      have ih_res := ih (by omega) _ (e + 1) (hn || isNot (gateAt C k).op) hF' hnoNot hmono
      have hnot_false : (hn || isNot (gateAt C k).op) = false := by
        clear ih_res hmono hF'
        suffices ∀ m' F' e' hn', (frontierAux n C m' (F', e', hn')).2.2 = false → hn' = false by
          exact this k _ _ _ hnoNot
        intro m'
        induction m' with
        | zero => intro _ _ _ h; exact h
        | succ j ihj =>
          intro F' e' hn' h
          simp only [frontierAux] at h
          split_ifs at h with h1
          · have := ihj _ _ _ h
            exact (by simpa using this : hn' = false ∧ _).1
          · exact ihj _ _ _ h
      have hop_ne_not : (gateAt C k).op ≠ .not := by
        intro hnot
        simp [hnot, isNot] at hnot_false
      have hg := hG (gateAt C k) (by simp [gateAt, List.getD, hk])
      intro w hw hwx
      by_cases hwk : w = n + k
      · subst hwk
        have hgx := wires_getD_gate C x k (hx ▸ hRB) hk
        have hgy := wires_getD_gate C y k (hy ▸ hRB) hk
        rw [hx] at hgx; rw [hy] at hgy
        rw [hgx] at hwx; rw [hgy]
        rcases hg.2 with hand | hor | ⟨hnot, _⟩
        · rw [hand] at hwx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at hwx ⊢
          intro i hi
          exact ih_res i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)) (hwx i hi)
        · rw [hor] at hwx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hwx ⊢
          rcases hwx with ⟨_, ⟨i, hi, rfl⟩, htrue⟩
          exact ⟨(C.wires y).getD i false, ⟨i, hi, rfl⟩,
            ih_res i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)) htrue⟩
        · exact absurd hnot hop_ne_not
      · exact ih_res w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩)) hwx
    · have hF' : ∀ w ∈ F, w < n + k := by
        intro w hw
        have := hF w hw
        have hne : w ≠ n + k := fun heq => hmem (heq ▸ hw)
        omega
      exact ih (by omega) F e hn hF' hnoNot hmono

lemma oneEach_length {N : ℕ} (x y : Fin N) : (oneEach x y).length = N + N := by
  simp [oneEach]

lemma oneEach_getD_left {N : ℕ} (x y : Fin N) (i : ℕ) (hi : i < N) :
    (oneEach x y).getD i false = decide (i = x.val) := by
  unfold oneEach
  rw [getD_append_lt _ _ _ _ (by simp [hi])]
  simp [List.getD, hi, Fin.ext_iff]

lemma oneEach_getD_right {N : ℕ} (x y : Fin N) (j : ℕ) (hj : j < N) :
    (oneEach x y).getD (N + j) false = decide (j = y.val) := by
  unfold oneEach
  simp [List.getD, List.getElem?_append_right, hj, Fin.ext_iff]

lemma area_le_A {N g d r s : ℕ} (hg : 0 < g) (hN : 2 * g + 1 < N)
    (hrs : r + s = g + 1) (hd0 : 0 < d) (hdrs : d ≤ r * s) (hrsN : r * s < N)
    (hmin : ∀ i : ℕ, i ≤ g + 1 → d ≤ i * (g + 1 - i) → r * s ≤ i * (g + 1 - i))
    (C : Circuit) (hleg : Legal N C) (hsize : C.size ≤ g)
    (harea_d : ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => C.eval (oneEach z.1 z.2) = true)).card ≤ (g + 1) * N - d) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => C.eval (oneEach z.1 z.2) = true)).card ≤ (g + 1) * N - r * s := by
  set tbl : Fin N → Fin N → Bool := fun x y => C.eval (oneEach x y)
  set T : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => tbl z.1 z.2 = true)
  set res := frontierAux (N + N) C C.gates.length ({C.output}, 0, false)
  have hinv := frontierAux_inv (N + N) C hleg.1 hleg.2.2 C.gates.length (le_refl _)
    {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1) (by simp)
  set F0 : Finset ℕ := res.1
  set SR : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => x.val ∈ F0)
  set SC : Finset (Fin N) := Finset.univ.filter (fun y : Fin N => N + y.val ∈ F0)
  have hSR_SC_card : SR.card + SC.card = F0.card := by
    have hdisj : Disjoint (SR.image Fin.val) (SC.image (fun y : Fin N => N + y.val)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rcases Finset.mem_image.mp hw1 with ⟨x, _, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨y, _, hy⟩
      omega
    have heq : SR.image Fin.val ∪ SC.image (fun y : Fin N => N + y.val) = F0 := by
      ext w
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, SR, SC]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) <;> assumption
      · intro hw
        have hwlt := hinv.1 w hw
        by_cases h : w < N
        · left; exact ⟨⟨w, h⟩, hw, rfl⟩
        · right
          have hw' : N + (w - N) = w := by omega
          exact ⟨⟨w - N, by omega⟩, by rwa [hw'], hw'⟩
    rw [← heq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
  have hF0_le : F0.card + (if res.2.2 then 1 else 0) ≤ g + 1 := by
    have h1 : F0.card + (if res.2.2 then 1 else 0) ≤ res.2.1 + 1 := hinv.2.1
    have h2 : res.2.1 ≤ 0 + C.gates.length := hinv.2.2
    have h3 : C.gates.length ≤ g := hsize
    omega
  have hab_le : SR.card + SC.card ≤ g + 1 := by omega
  have hSR_lt : SR.card < N := by omega
  have hSC_lt : SC.card < N := by omega
  obtain ⟨x0, hx0⟩ : ∃ x : Fin N, x ∉ SR := by
    by_contra hall; push_neg at hall
    have : SR = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hSR_lt; omega
  obtain ⟨y0, hy0⟩ : ∃ y : Fin N, y ∉ SC := by
    by_contra hall; push_neg at hall
    have : SC = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hSC_lt; omega
  have h_agree : ∀ x₁ y₁ x₂ y₂ : Fin N,
      (∀ x ∈ SR, (x = x₁ ↔ x = x₂)) → (∀ y ∈ SC, (y = y₁ ↔ y = y₂)) →
      tbl x₁ y₁ = tbl x₂ y₂ := by
    intro x₁ y₁ x₂ y₂ hxr hyc
    apply frontierAux_agree (N + N) C hleg.1 (oneEach x₁ y₁) (oneEach x₂ y₂)
      (oneEach_length x₁ y₁) (oneEach_length x₂ y₂) C.gates.length (le_refl _)
      {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1)
    · intro w hw
      have hwlt := hinv.1 w hw
      by_cases h : w < N
      · rw [oneEach_getD_left x₁ y₁ w h, oneEach_getD_left x₂ y₂ w h]
        have hmem : (⟨w, h⟩ : Fin N) ∈ SR := by simp [SR, F0, res, hw]
        have hiff := hxr ⟨w, h⟩ hmem
        simp [Fin.ext_iff] at hiff
        simp [hiff]
      · have hj : w - N < N := by omega
        have hw_eq : w = N + (w - N) := by omega
        rw [hw_eq, oneEach_getD_right x₁ y₁ (w - N) hj, oneEach_getD_right x₂ y₂ (w - N) hj]
        have hmem : (⟨w - N, hj⟩ : Fin N) ∈ SC := by simp [SC, F0, res, ← hw_eq, hw]
        have hiff := hyc ⟨w - N, hj⟩ hmem
        simp [Fin.ext_iff] at hiff
        simp [hiff]
    · simp
  have hout_false : ∀ x y : Fin N, x ∉ SR → y ∉ SC → tbl x y = false := by
    have hconst : ∀ x y : Fin N, x ∉ SR → y ∉ SC → tbl x y = tbl x0 y0 := by
      intro x y hx hy
      apply h_agree x y x0 y0
      · intro a ha; constructor <;> intro h <;> subst h <;> contradiction
      · intro b hb; constructor <;> intro h <;> subst h <;> contradiction
    cases h0 : tbl x0 y0
    · intro x y hx hy; rw [hconst x y hx hy, h0]
    · exfalso
      have hsub : SRᶜ ×ˢ SCᶜ ⊆ T := by
        intro z hz
        simp only [Finset.mem_product, Finset.mem_compl] at hz
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hconst z.1 z.2 hz.1 hz.2, h0]
      have hcard_le := Finset.card_le_card hsub
      rw [Finset.card_product, Finset.card_compl, Finset.card_compl, Fintype.card_fin] at hcard_le
      have h1 : (N - SR.card) * (N - SC.card) ≥ (N - (g + 1)) * N := by
        have h2 : SR.card * N + SC.card * N ≤ (g + 1) * N := by
          rw [← Nat.add_mul]; exact Nat.mul_le_mul_right N hab_le
        have h3 : (N - SR.card) * (N - SC.card) + SR.card * N + SC.card * N =
            N * N + SR.card * SC.card := by
          zify [le_of_lt hSR_lt, le_of_lt hSC_lt]; ring
        have h4 : (N - (g + 1)) * N + (g + 1) * N = N * N := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        omega
      have h5 : (g + 1) * N ≤ (N - (g + 1)) * N := Nat.mul_le_mul_right N (by omega)
      have hpos : 0 < (g + 1) * N := Nat.mul_pos (by omega) (by omega)
      change T.card ≤ (g + 1) * N - d at harea_d
      omega
  set U : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => z.1 ∈ SR ∨ z.2 ∈ SC)
  have hT_sub_U : T ⊆ U := by
    intro z hz
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hnot
    push_neg at hnot
    have := hout_false z.1 z.2 hnot.1 hnot.2
    rw [this] at hz; exact Bool.false_ne_true hz
  have hU_card : U.card = (SR.card + SC.card) * N - SR.card * SC.card := by
    have hU_eq : U = (SR ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ SC) := by
      ext z; simp [U]
    have hU_inter : (SR ×ˢ Finset.univ) ∩ (Finset.univ ×ˢ SC) = SR ×ˢ SC := by
      ext z; simp
    have hinc := Finset.card_union_add_card_inter (SR ×ˢ (Finset.univ : Finset (Fin N)))
      ((Finset.univ : Finset (Fin N)) ×ˢ SC)
    rw [← hU_eq, hU_inter, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_univ, Fintype.card_fin] at hinc
    have hmul : SR.card * SC.card ≤ SR.card * N + N * SC.card := by
      calc SR.card * SC.card ≤ SR.card * N := Nat.mul_le_mul_left _ (le_of_lt hSC_lt)
        _ ≤ SR.card * N + N * SC.card := Nat.le_add_right _ _
    have hadd : (SR.card + SC.card) * N = SR.card * N + N * SC.card := by ring
    omega
  have hT_le_U : T.card ≤ (SR.card + SC.card) * N - SR.card * SC.card := by
    rw [← hU_card]; exact Finset.card_le_card hT_sub_U
  by_cases hsum_le : SR.card + SC.card ≤ g
  · have h1 : (SR.card + SC.card) * N ≤ g * N := Nat.mul_le_mul_right N hsum_le
    have h2 : g * N + N = (g + 1) * N := by ring
    omega
  · have hsum_eq : SR.card + SC.card = g + 1 := by omega
    by_cases hprod : d ≤ SR.card * SC.card
    · have hge := hmin SR.card (by omega) (by rwa [show g + 1 - SR.card = SC.card by omega])
      rw [show g + 1 - SR.card = SC.card by omega] at hge
      rw [hsum_eq] at hT_le_U
      omega
    · have hprod_lt : SR.card * SC.card < d := by omega
      have hnoNot : res.2.2 = false := by
        cases h : res.2.2
        · rfl
        · rw [h] at hF0_le; simp at hF0_le; omega
      by_cases hrow_false : ∃ x ∈ SR, tbl x y0 = false
      · rcases hrow_false with ⟨x1, hx1, hfx1⟩
        set Bad : Finset (Fin N × Fin N) := {x1} ×ˢ SCᶜ
        have hBad_sub : Bad ⊆ U \ T := by
          intro z hz
          simp only [Bad, Finset.mem_product, Finset.mem_singleton, Finset.mem_compl] at hz
          rcases hz with ⟨hz1, hy⟩
          simp only [Finset.mem_sdiff, U, T, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨Or.inl (hz1 ▸ hx1), ?_⟩
          have heq : tbl z.1 z.2 = tbl x1 y0 := by
            rw [hz1]
            apply h_agree x1 z.2 x1 y0 (fun _ _ => Iff.rfl)
            intro b hb; constructor <;> intro h <;> subst h <;> contradiction
          rw [heq, hfx1]; decide
        have hcard_bad : Bad.card = N - SC.card := by
          simp [Bad, Finset.card_product, Finset.card_compl, Fintype.card_fin]
        have hdiff := Finset.card_le_card hBad_sub
        rw [hcard_bad, Finset.card_sdiff_of_subset hT_sub_U, hU_card, hsum_eq] at hdiff
        have h1 : g * N + N = (g + 1) * N := by ring
        have hSR_pos : 0 < SR.card := Finset.card_pos.mpr ⟨x1, hx1⟩
        have h2 : SC.card ≤ SR.card * SC.card := Nat.le_mul_of_pos_left SC.card hSR_pos
        omega
      · by_cases hcol_false : ∃ y ∈ SC, tbl x0 y = false
        · rcases hcol_false with ⟨y1, hy1, hfy1⟩
          set Bad : Finset (Fin N × Fin N) := SRᶜ ×ˢ {y1}
          have hBad_sub : Bad ⊆ U \ T := by
            intro z hz
            simp only [Bad, Finset.mem_product, Finset.mem_singleton, Finset.mem_compl] at hz
            rcases hz with ⟨hx, hz2⟩
            simp only [Finset.mem_sdiff, U, T, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨Or.inr (hz2 ▸ hy1), ?_⟩
            have heq : tbl z.1 z.2 = tbl x0 y1 := by
              rw [hz2]
              apply h_agree z.1 y1 x0 y1
              · intro a ha; constructor <;> intro h <;> subst h <;> contradiction
              · exact fun _ _ => Iff.rfl
            rw [heq, hfy1]; decide
          have hcard_bad : Bad.card = N - SR.card := by
            simp [Bad, Finset.card_product, Finset.card_compl, Fintype.card_fin]
          have hdiff := Finset.card_le_card hBad_sub
          rw [hcard_bad, Finset.card_sdiff_of_subset hT_sub_U, hU_card, hsum_eq] at hdiff
          have h1 : g * N + N = (g + 1) * N := by ring
          have hSC_pos : 0 < SC.card := Finset.card_pos.mpr ⟨y1, hy1⟩
          have h2 : SR.card ≤ SR.card * SC.card := Nat.le_mul_of_pos_right SR.card hSC_pos
          omega
        · exfalso
          push_neg at hrow_false hcol_false
          have hU_sub_T : U ⊆ T := by
            intro z hz
            simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hz
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hz with hx | hy
            · have hbase : tbl z.1 y0 = true := Bool.eq_true_of_not_eq_false (hrow_false z.1 hx)
              apply frontierAux_mono (N + N) C hleg.1 hleg.2.2 (oneEach z.1 y0) (oneEach z.1 z.2)
                (oneEach_length _ _) (oneEach_length _ _) C.gates.length (le_refl _)
                {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1) hnoNot
              · intro w hw hwt
                have hwlt := hinv.1 w hw
                by_cases h : w < N
                · rw [oneEach_getD_left z.1 y0 w h] at hwt
                  rw [oneEach_getD_left z.1 z.2 w h]; exact hwt
                · have hj : w - N < N := by omega
                  have hw_eq : w = N + (w - N) := by omega
                  rw [hw_eq, oneEach_getD_right z.1 y0 (w - N) hj] at hwt
                  have hyeq : (⟨w - N, hj⟩ : Fin N) = y0 := Fin.ext (of_decide_eq_true hwt)
                  have hmem : (⟨w - N, hj⟩ : Fin N) ∈ SC := by simp [SC, F0, res, ← hw_eq, hw]
                  rw [hyeq] at hmem; exact absurd hmem hy0
              · simp
              · exact hbase
            · have hbase : tbl x0 z.2 = true := Bool.eq_true_of_not_eq_false (hcol_false z.2 hy)
              apply frontierAux_mono (N + N) C hleg.1 hleg.2.2 (oneEach x0 z.2) (oneEach z.1 z.2)
                (oneEach_length _ _) (oneEach_length _ _) C.gates.length (le_refl _)
                {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1) hnoNot
              · intro w hw hwt
                have hwlt := hinv.1 w hw
                by_cases h : w < N
                · rw [oneEach_getD_left x0 z.2 w h] at hwt
                  have hxeq : (⟨w, h⟩ : Fin N) = x0 := Fin.ext (of_decide_eq_true hwt)
                  have hmem : (⟨w, h⟩ : Fin N) ∈ SR := by simp [SR, F0, res, hw]
                  rw [hxeq] at hmem; exact absurd hmem hx0
                · have hj : w - N < N := by omega
                  have hw_eq : w = N + (w - N) := by omega
                  rw [hw_eq, oneEach_getD_right x0 z.2 (w - N) hj] at hwt
                  rw [hw_eq, oneEach_getD_right z.1 z.2 (w - N) hj]; exact hwt
              · simp
              · exact hbase
          have hT_eq_U : T.card = U.card := le_antisymm (Finset.card_le_card hT_sub_U)
            (Finset.card_le_card hU_sub_T)
          rw [hU_card, hsum_eq] at hT_eq_U
          have hmul_le : SR.card * SC.card ≤ (g + 1) * N := by
            have : SR.card * SC.card < N := by omega
            have : 1 * N ≤ (g + 1) * N := Nat.mul_le_mul_right N (by omega)
            omega
          have hd_le : d ≤ (g + 1) * N := by
            have : 1 * N ≤ (g + 1) * N := Nat.mul_le_mul_right N (by omega)
            omega
          change T.card ≤ (g + 1) * N - d at harea_d
          omega

def targetI (N t u : ℕ) (x y : Fin N) : Bool :=
  decide ((y.val + N - x.val + N - u % N) % N < t)

lemma card_targetI_col {N t : ℕ} (ht : t ≤ N) (u : ℕ) (x : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun y => targetI N t u x y = true)).card = t := by
  have hN : 0 < N := by exact Fin.pos x
  let f : Fin N → Fin N := fun y => ⟨(y.val + N - x.val + N - u % N) % N, Nat.mod_lt _ hN⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro y₁ y₂ h
    have hv := congrArg Fin.val h
    simp only [f] at hv
    have hx := x.isLt; have hu := Nat.mod_lt u hN
    have hy1 := y₁.isLt; have hy2 := y₂.isLt
    have h1 : (y₁.val + (N - x.val) + (N - u % N)) % N = (y₂.val + (N - x.val) + (N - u % N)) % N := by
      have e1 : y₁.val + N - x.val + N - u % N = y₁.val + (N - x.val) + (N - u % N) := by omega
      have e2 : y₂.val + N - x.val + N - u % N = y₂.val + (N - x.val) + (N - u % N) := by omega
      rw [← e1, ← e2]; exact hv
    have h2 : (y₁.val + ((N - x.val) + (N - u % N))) % N =
        (y₂.val + ((N - x.val) + (N - u % N))) % N := by
      simpa [Nat.add_assoc] using h1
    apply Fin.ext
    have h3 : (y₁.val + ((N - x.val) + (N - u % N))) % N =
        (y₁.val + ((N - x.val) + (N - u % N)) % N) % N := by
      rw [Nat.add_mod, Nat.add_mod y₁.val, Nat.mod_mod]
    have h4 : (y₂.val + ((N - x.val) + (N - u % N))) % N =
        (y₂.val + ((N - x.val) + (N - u % N)) % N) % N := by
      rw [Nat.add_mod, Nat.add_mod y₂.val, Nat.mod_mod]
    set c := ((N - x.val) + (N - u % N)) % N
    have hc : c < N := Nat.mod_lt _ hN
    rw [h3, h4] at h2
    by_cases h1c : y₁.val + c < N <;> by_cases h2c : y₂.val + c < N
    · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_of_lt h2c] at h2; omega
    · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at h2; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt h2c] at h2; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h2; omega
  let e := Equiv.ofBijective f hbij
  have hcard : ((Finset.univ : Finset (Fin N)).filter (fun y => (f y).val < t)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card := by
    refine Finset.card_bij (fun y _ => f y) (fun y hy => by simpa using hy)
      (fun a _ b _ h => hbij.1 h) (fun z hz => ?_)
    obtain ⟨y, hy⟩ := hbij.2 z
    exact ⟨y, by simpa [hy] using hz, hy⟩
  have hlt : ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card = t := by
    refine (Finset.card_bij (fun z _ => z.val) (fun z hz => by simp at hz ⊢; exact hz)
      (fun a _ b _ h => Fin.ext h) (fun k hk => ?_)).trans (Finset.card_range t)
    simp at hk
    exact ⟨⟨k, by omega⟩, by simp [hk], rfl⟩
  simpa [targetI, f] using hcard.trans hlt

lemma card_targetI_row {N t : ℕ} (ht : t ≤ N) (u : ℕ) (y : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun x => targetI N t u x y = true)).card = t := by
  have hN : 0 < N := Fin.pos y
  let f : Fin N → Fin N := fun x => ⟨(y.val + N - x.val + N - u % N) % N, Nat.mod_lt _ hN⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro x₁ x₂ h
    have hv := congrArg Fin.val h
    simp only [f] at hv
    have hy := y.isLt; have hu := Nat.mod_lt u hN
    have hx1 := x₁.isLt; have hx2 := x₂.isLt
    have h1 : ((N - x₁.val) + (y.val + (N - u % N))) % N =
        ((N - x₂.val) + (y.val + (N - u % N))) % N := by
      have e1 : y.val + N - x₁.val + N - u % N = (N - x₁.val) + (y.val + (N - u % N)) := by omega
      have e2 : y.val + N - x₂.val + N - u % N = (N - x₂.val) + (y.val + (N - u % N)) := by omega
      rw [← e1, ← e2]; exact hv
    set c := (y.val + (N - u % N)) % N
    have hc : c < N := Nat.mod_lt _ hN
    have h3 : ((N - x₁.val) + (y.val + (N - u % N))) % N = ((N - x₁.val) + c) % N := by
      rw [Nat.add_mod, Nat.add_mod (N - x₁.val), Nat.mod_mod]
    have h4 : ((N - x₂.val) + (y.val + (N - u % N))) % N = ((N - x₂.val) + c) % N := by
      rw [Nat.add_mod, Nat.add_mod (N - x₂.val), Nat.mod_mod]
    rw [h3, h4] at h1
    apply Fin.ext
    by_cases h1c : N - x₁.val + c < N <;> by_cases h2c : N - x₂.val + c < N
    · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_of_lt h2c] at h1; omega
    · have hlt2 : N - x₂.val + c - N < N := by omega
      rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at h1
      omega
    · have hlt1 : N - x₁.val + c - N < N := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt h2c] at h1
      omega
    · have hlt1 : N - x₁.val + c - N < N := by omega
      have hlt2 : N - x₂.val + c - N < N := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at h1
      omega
  have hcard : ((Finset.univ : Finset (Fin N)).filter (fun x => (f x).val < t)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card := by
    refine Finset.card_bij (fun x _ => f x) (fun x hx => by simpa using hx)
      (fun a _ b _ h => hbij.1 h) (fun z hz => ?_)
    obtain ⟨x, hx⟩ := hbij.2 z
    exact ⟨x, by simpa [hx] using hz, hx⟩
  have hlt : ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card = t := by
    refine (Finset.card_bij (fun z _ => z.val) (fun z hz => by simp at hz ⊢; exact hz)
      (fun a _ b _ h => Fin.ext h) (fun k hk => ?_)).trans (Finset.card_range t)
    simp at hk
    exact ⟨⟨k, by omega⟩, by simp [hk], rfl⟩
  simpa [targetI, f] using hcard.trans hlt

lemma card_targetI_u {N t : ℕ} (ht : t ≤ N) (x y : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun u : Fin N => targetI N t u.val x y = true)).card = t := by
  have hN : 0 < N := Fin.pos x
  have heq : (Finset.univ : Finset (Fin N)).filter (fun u : Fin N => targetI N t u.val x y = true) =
      (Finset.univ : Finset (Fin N)).filter (fun u : Fin N => targetI N t x.val u y = true) := by
    apply Finset.filter_congr
    intro u _
    simp only [targetI, Nat.mod_eq_of_lt u.isLt, Nat.mod_eq_of_lt x.isLt]
    have h1 : y.val + N - x.val + N - u.val = y.val + N - u.val + N - x.val := by
      have := x.isLt; have := u.isLt; omega
    rw [h1]
  rw [heq]
  exact card_targetI_row ht x.val y

lemma card_targetI_all {N t : ℕ} (ht : t ≤ N) (u : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => targetI N t u z.1 z.2 = true)).card =
      N * t := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ x : Fin N, ∑ y : Fin N, (if targetI N t u x y = true then 1 else 0) = t := by
    intro x
    rw [← Finset.card_filter]
    exact card_targetI_col ht u x
  simp [hinner]

lemma loss_add_two_overlap {N t : ℕ} (ht : t ≤ N) (P : Fin N × Fin N → Bool) (u : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z ≠ targetI N t u z.1 z.2)).card +
      2 * ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => P z = true ∧ targetI N t u z.1 z.2 = true)).card =
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card + N * t := by
  rw [← card_targetI_all ht u]
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  cases P z <;> cases targetI N t u z.1 z.2 <;> simp

lemma sum_overlap_eq {N t : ℕ} (ht : t ≤ N) (P : Fin N × Fin N → Bool) :
    ∑ u : Fin N, ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => P z = true ∧ targetI N t u.val z.1 z.2 = true)).card =
    t * ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hp : P z = true
  · simp only [hp, true_and, ↓reduceIte, mul_one]
    rw [← Finset.card_filter]
    exact card_targetI_u ht z.1 z.2
  · simp [hp]

lemma sum_loss_eq {N t : ℕ} (hNt : N < 2 * t) (ht : t ≤ N) (P : Fin N × Fin N → Bool) :
    ∑ u : Fin N, ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => P z ≠ targetI N t u.val z.1 z.2)).card +
      (2 * t - N) * ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card =
    N * (N * t) := by
  have hsum : ∑ u : Fin N, (((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => P z ≠ targetI N t u.val z.1 z.2)).card +
      2 * ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => P z = true ∧ targetI N t u.val z.1 z.2 = true)).card) =
      ∑ _u : Fin N, (((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card +
        N * t) := by
    apply Finset.sum_congr rfl
    intro u _
    exact loss_add_two_overlap ht P u.val
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_overlap_eq ht P,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  set a := ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card
  have h1 : 2 * (t * a) = (2 * t - N) * a + N * a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega), Nat.mul_assoc]
  have h2 : N * (a + N * t) = N * a + N * (N * t) := by ring
  omega

def orChain (n : ℕ) (w0 : ℕ) (ws : List ℕ) : Circuit :=
  { gates := (List.range ws.length).zipWith
      (fun k w => ⟨GateOp.or, [if k = 0 then w0 else n + k - 1, w]⟩) ws
    output := if ws.length = 0 then w0 else n + ws.length - 1 }

lemma orChain_size (n w0 : ℕ) (ws : List ℕ) : (orChain n w0 ws).size = ws.length := by
  simp [Circuit.size, orChain]

lemma orChain_readsBack (n w0 : ℕ) (ws : List ℕ) (hw0 : w0 < n) (hws : ∀ w ∈ ws, w < n) :
    ReadsBack n (orChain n w0 ws) := by
  intro j hj i hi
  simp only [orChain, List.length_zipWith, List.length_range, min_self] at hj
  have hgate : gateAt (orChain n w0 ws) j =
      ⟨GateOp.or, [if j = 0 then w0 else n + j - 1, ws[j]]⟩ := by
    simp [gateAt, orChain, List.getD, hj]
  rw [hgate] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · split_ifs <;> omega
  · have := hws ws[j] (List.getElem_mem hj)
    omega

lemma orChain_legal (N w0 : ℕ) (ws : List ℕ) (hw0 : w0 < N + N)
    (hws : ∀ w ∈ ws, w < N + N) : Legal N (orChain (N + N) w0 ws) := by
  refine ⟨orChain_readsBack (N + N) w0 ws hw0 hws, ?_, ?_⟩
  · rw [orChain_size]
    simp only [orChain]
    split_ifs <;> omega
  · intro gate hgate
    rw [List.mem_iff_getElem] at hgate
    rcases hgate with ⟨j, hj, rfl⟩
    simp [orChain]

lemma orChain_eval (n w0 : ℕ) (ws : List ℕ) (hw0 : w0 < n) (hws : ∀ w ∈ ws, w < n)
    (x : List Bool) (hx : x.length = n) :
    (orChain n w0 ws).eval x = (w0 :: ws).any (fun w => x.getD w false) := by
  have hRB := orChain_readsBack n w0 ws hw0 hws
  have hwire : ∀ j < ws.length,
      ((orChain n w0 ws).wires x).getD (n + j) false =
        (w0 :: ws.take (j + 1)).any (fun w => x.getD w false) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hgt := wires_getD_gate (orChain n w0 ws) x 0 (hx ▸ hRB) (by simp [orChain, hj])
      rw [hx] at hgt
      have hga : gateAt (orChain n w0 ws) 0 = ⟨GateOp.or, [w0, ws[0]]⟩ := by
        simp [gateAt, orChain, List.getD, hj]
      rw [hgt, hga]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [wires_getD_input _ _ w0 (by omega),
        wires_getD_input _ _ ws[0] (by have := hws ws[0] (List.getElem_mem hj); omega)]
      rw [List.take_succ_eq_append_getElem hj]
      simp
    | succ k ih =>
      intro hj
      have hgt := wires_getD_gate (orChain n w0 ws) x (k + 1) (hx ▸ hRB)
        (by simp [orChain, hj])
      rw [hx] at hgt
      have hga : gateAt (orChain n w0 ws) (k + 1) = ⟨GateOp.or, [n + k, ws[k + 1]]⟩ := by
        simp [gateAt, orChain, List.getD, hj]
      rw [hgt, hga]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [ih (by omega),
        wires_getD_input _ _ ws[k + 1] (by have := hws ws[k + 1] (List.getElem_mem hj); omega)]
      rw [List.take_succ_eq_append_getElem hj]
      simp only [List.any_cons, List.any_append, List.any_nil, Bool.or_false]
      exact Bool.or_assoc _ _ _
  cases hlen : ws.length with
  | zero =>
    have hws_nil : ws = [] := List.eq_nil_of_length_eq_zero hlen
    subst hws_nil
    simp only [Circuit.eval, orChain, List.length_nil, ↓reduceIte, List.any_cons, List.any_nil,
      Bool.or_false]
    exact wires_getD_input _ _ w0 (by omega)
  | succ m =>
    have h1 := hwire m (by omega)
    rw [show m + 1 = ws.length from hlen.symm, List.take_length] at h1
    simpa [Circuit.eval, orChain, hlen] using h1

def rowMap (N t : ℕ) (hN : 0 < N) (a : ℕ) : Fin N :=
  let L := N / Nat.gcd N t
  ⟨(a / L + (a % L) * t) % N, Nat.mod_lt _ hN⟩

lemma rowMap_inj {N t r : ℕ} (hN : 0 < N) (hr : r < N) :
    ∀ a₁ ∈ Finset.range r, ∀ a₂ ∈ Finset.range r,
      rowMap N t hN a₁ = rowMap N t hN a₂ → a₁ = a₂ := by
  intro a₁ ha₁ a₂ ha₂ heq
  simp only [Finset.mem_range] at ha₁ ha₂
  have hv := congrArg Fin.val heq
  simp only [rowMap] at hv
  set d0 := Nat.gcd N t
  set L := N / d0
  have hd0_pos : 0 < d0 := Nat.gcd_pos_of_pos_left t hN
  have hd0_N : d0 ∣ N := Nat.gcd_dvd_left N t
  have hd0_t : d0 ∣ t := Nat.gcd_dvd_right N t
  have hLd0 : L * d0 = N := Nat.div_mul_cancel hd0_N
  have hL_pos : 0 < L := by
    by_contra h; push_neg at h; interval_cases L; simp at hLd0; omega
  have hq1 : a₁ / L < d0 := by
    rw [Nat.div_lt_iff_lt_mul hL_pos, Nat.mul_comm, hLd0]; omega
  have hq2 : a₂ / L < d0 := by
    rw [Nat.div_lt_iff_lt_mul hL_pos, Nat.mul_comm, hLd0]; omega
  have hmod_d0 : (a₁ / L + (a₁ % L) * t) % d0 = (a₂ / L + (a₂ % L) * t) % d0 := by
    rw [← Nat.mod_mod_of_dvd _ hd0_N, hv, Nat.mod_mod_of_dvd _ hd0_N]
  have hd0_mul : ∀ m, (m * t) % d0 = 0 := fun m => Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_of_dvd_right hd0_t m)
  rw [Nat.add_mod, hd0_mul, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hq1,
    Nat.add_mod, hd0_mul, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hq2] at hmod_d0
  rw [hmod_d0] at hv
  set r₁ := a₁ % L
  set r₂ := a₂ % L
  have hr1 : r₁ < L := Nat.mod_lt a₁ hL_pos
  have hr2 : r₂ < L := Nat.mod_lt a₂ hL_pos
  have hcop : Nat.Coprime L (t / d0) := by
    have := Nat.coprime_div_gcd_div_gcd hd0_pos (m := N) (n := t)
    simpa [L, d0] using this
  have hdiv_L : ∀ x y, x < L → y < L → x ≤ y →
      (a₂ / L + x * t) % N = (a₂ / L + y * t) % N → x = y := by
    intro x y hx hy hxy hmod
    have hdvdN : N ∣ (y - x) * t := by
      have hmod2 : (x * t) % N = (y * t) % N := by
        have hsub := congrArg (fun z => (z + N - (a₂ / L) % N) % N) hmod
        have hlt_q : a₂ / L < N := by
          have : a₂ / L ≤ a₂ := Nat.div_le_self a₂ L; omega
        have hsimp : ∀ v, ((a₂ / L + v) % N + N - (a₂ / L) % N) % N = v % N := by
          intro v
          rw [Nat.mod_eq_of_lt hlt_q]
          have h1 : (a₂ / L + v) % N + N - a₂ / L = (a₂ / L + v) % N + (N - a₂ / L) := by omega
          rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have h2 : a₂ / L + v + (N - a₂ / L) = v + N := by omega
          rw [h2, Nat.add_mod_right]
        simpa [hsimp] using hsub
      have hle : x * t ≤ y * t := Nat.mul_le_mul_right t hxy
      rw [Nat.sub_mul]
      exact (Nat.modEq_iff_dvd' hle).mp hmod2
    have hteq : t = (t / d0) * d0 := (Nat.div_mul_cancel hd0_t).symm
    have hdvd' : L * d0 ∣ ((y - x) * (t / d0)) * d0 := by
      rw [hLd0, Nat.mul_assoc, ← hteq]; exact hdvdN
    have hdvdL : L ∣ (y - x) * (t / d0) := (Nat.mul_dvd_mul_iff_right hd0_pos).mp hdvd'
    have hdvd_sub : L ∣ y - x := hcop.dvd_of_dvd_mul_right hdvdL
    have : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_sub (by omega)
    omega
  have hr_eq : r₁ = r₂ := by
    rcases le_total r₁ r₂ with hle | hle
    · exact hdiv_L r₁ r₂ hr1 hr2 hle hv
    · exact (hdiv_L r₂ r₁ hr2 hr1 hle hv.symm).symm
  have h1 := Nat.div_add_mod a₁ L
  have h2 := Nat.div_add_mod a₂ L
  have hr_eq' : a₁ % L = a₂ % L := hr_eq
  rw [← h1, ← h2, hmod_d0, hr_eq']

lemma count_mod_in_range (N B w : ℕ) (hN : 0 < N) (hw : w < N) :
    ((Finset.range B).filter (fun v => v % N = w)).card =
      B / N + (if w < B % N then 1 else 0) := by
  set k := B / N + (if w < B % N then 1 else 0)
  refine (Finset.card_bij (fun v _ => v / N) ?_ ?_ ?_).trans (Finset.card_range k)
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range, k] at hv ⊢
    have hdiv := Nat.div_add_mod v N
    have hB := Nat.div_add_mod B N
    have hBm : B % N < N := Nat.mod_lt B hN
    have hlt_mul : N * (v / N) + w < N * (B / N) + B % N := by
      rw [← hv.2, hdiv, hB]; exact hv.1
    split_ifs with hlt
    · have : N * (v / N) < N * (B / N + 1) := by rw [Nat.mul_add, mul_one]; omega
      exact (Nat.mul_lt_mul_left hN).mp this
    · have : N * (v / N) < N * (B / N) := by omega
      exact (Nat.mul_lt_mul_left hN).mp this
  · intro v₁ hv₁ v₂ hv₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hv₁ hv₂
    have h1 := Nat.div_add_mod v₁ N
    have h2 := Nat.div_add_mod v₂ N
    rw [← h1, ← h2, heq, hv₁.2, hv₂.2]
  · intro q hq
    simp only [Finset.mem_range, k] at hq
    refine ⟨q * N + w, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      have hB := Nat.div_add_mod B N
      refine ⟨?_, ?_⟩
      · split_ifs at hq with hlt
        · have : q ≤ B / N := by omega
          have : q * N ≤ (B / N) * N := Nat.mul_le_mul_right N this
          rw [Nat.mul_comm (B / N) N] at this; omega
        · have : q + 1 ≤ B / N := by omega
          have : (q + 1) * N ≤ (B / N) * N := Nat.mul_le_mul_right N this
          rw [Nat.add_mul, one_mul, Nat.mul_comm (B / N) N] at this; omega
      · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hw]
    · rw [Nat.mul_comm q N, Nat.mul_add_div hN, Nat.div_eq_of_lt hw, add_zero]

lemma mod_add_left_eq (a b c N : ℕ) (h : a % N = b % N) : (a + c) % N = (b + c) % N := by
  rw [Nat.add_mod, h, ← Nat.add_mod]

lemma mod_add_right_eq (a b c N : ℕ) (h : b % N = c % N) : (a + b) % N = (a + c) % N := by
  rw [Nat.add_mod, h, ← Nat.add_mod]

lemma count_mod_in_block (N t j w : ℕ) (hN : 0 < N) (ht : t ≤ N) (hw : w < N) :
    ((Finset.Ico (j * t) ((j + 1) * t)).filter (fun v => v % N = w)).card =
      if (w + N - (j * t) % N) % N < t then 1 else 0 := by
  set r0 := (j * t) % N
  set d := (w + N - r0) % N
  have hr0 : r0 < N := Nat.mod_lt _ hN
  have hd : d < N := Nat.mod_lt _ hN
  have hmod_add : (j * t + d) % N = w := by
    calc (j * t + d) % N = (r0 + d) % N := mod_add_left_eq _ _ _ _ (Nat.mod_eq_of_lt hr0).symm
      _ = (r0 + (w + N - r0)) % N := mod_add_right_eq _ _ _ _ (Nat.mod_mod _ _)
      _ = (w + N) % N := by congr 1; omega
      _ = w := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hw]
  split_ifs with hlt
  · rw [Finset.card_eq_one]
    refine ⟨j * t + d, ?_⟩
    ext v
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hv1, hv2⟩, hvmod⟩
      set e := v - j * t
      have he : e < t := by rw [Nat.add_mul, one_mul] at hv2; omega
      have hveq : v = j * t + e := by omega
      have hmod_e : (r0 + e) % N = w := by
        rw [← hvmod, hveq]
        exact mod_add_left_eq _ _ _ _ (Nat.mod_eq_of_lt hr0)
      have hed : e = d := by
        have h1 : (r0 + e + (N - r0)) % N = (w + (N - r0)) % N :=
          mod_add_left_eq _ _ _ _ (by rw [hmod_e, Nat.mod_eq_of_lt hw])
        have h2 : r0 + e + (N - r0) = e + N := by omega
        have h3 : w + (N - r0) = w + N - r0 := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : e < N), h3] at h1
        exact h1
      omega
    · rintro rfl
      refine ⟨⟨by omega, ?_⟩, hmod_add⟩
      rw [Nat.add_mul, one_mul]; omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv hvmod
    simp only [Finset.mem_Ico] at hv
    set e := v - j * t
    have he : e < t := by rw [Nat.add_mul, one_mul] at hv; omega
    have hveq : v = j * t + e := by omega
    have hmod_e : (r0 + e) % N = w := by
      rw [← hvmod, hveq]
      exact mod_add_left_eq _ _ _ _ (Nat.mod_eq_of_lt hr0)
    have h1 : (r0 + e + (N - r0)) % N = (w + (N - r0)) % N :=
      mod_add_left_eq _ _ _ _ (by rw [hmod_e, Nat.mod_eq_of_lt hw])
    have h2 : r0 + e + (N - r0) = e + N := by omega
    have h3 : w + (N - r0) = w + N - r0 := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : e < N), h3] at h1
    omega

lemma inner_sum_rowMap {N t r : ℕ} (hN : 0 < N) (ht : t ≤ N) (hr : r < N) (z : Fin N) :
    ∑ a ∈ Finset.range r, (if (z.val + N - (rowMap N t hN a).val) % N < t then 1 else 0) =
      (r * t) / N + (if (z.val + N - r / (N / Nat.gcd N t)) % N < (r * t) % N then 1 else 0) := by
  set d0 := Nat.gcd N t
  set L := N / d0
  have hd0_pos : 0 < d0 := Nat.gcd_pos_of_pos_left t hN
  have hd0_N : d0 ∣ N := Nat.gcd_dvd_left N t
  have hd0_t : d0 ∣ t := Nat.gcd_dvd_right N t
  have hLd0 : L * d0 = N := Nat.div_mul_cancel hd0_N
  have hL_pos : 0 < L := by
    by_contra h; push_neg at h; interval_cases L; simp at hLd0; omega
  set q := r / L
  set m := r % L
  have hr_eq : r = q * L + m := (Nat.div_add_mod' r L).symm
  have hq_lt : q < d0 := by rw [Nat.div_lt_iff_lt_mul hL_pos, Nat.mul_comm, hLd0]; omega
  have hq_ltN : q < N := by have : q ≤ r := Nat.div_le_self r L; omega
  have hrange_split : Finset.range r = Finset.range (q * L) ∪ Finset.Ico (q * L) (q * L + m) := by
    ext a; simp [hr_eq]; omega
  have hdisj : Disjoint (Finset.range (q * L)) (Finset.Ico (q * L) (q * L + m)) := by
    rw [Finset.disjoint_left]; intro a h1 h2; simp at h1 h2; omega
  rw [hrange_split, Finset.sum_union hdisj]

  have hfull : ∑ a ∈ Finset.range (q * L),
      (if (z.val + N - (rowMap N t hN a).val) % N < t then 1 else 0) = q * (t / d0) := by
    have hsplit : ∑ a ∈ Finset.range (q * L),
        (if (z.val + N - (rowMap N t hN a).val) % N < t then 1 else 0) =
        ∑ k ∈ Finset.range q, ∑ j ∈ Finset.range L,
          (if (z.val + N - (rowMap N t hN (k * L + j)).val) % N < t then 1 else 0) := by
      have heq : (Finset.range (q * L)).sum (fun a =>
          if (z.val + N - (rowMap N t hN a).val) % N < t then 1 else 0) =
        ((Finset.range q) ×ˢ (Finset.range L)).sum (fun p =>
          if (z.val + N - (rowMap N t hN (p.1 * L + p.2)).val) % N < t then 1 else 0) := by
        symm
        refine Finset.sum_bij (fun p _ => p.1 * L + p.2) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro p hp
          simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
          have : (p.1 + 1) * L ≤ q * L := Nat.mul_le_mul_right L (by omega)
          rw [Nat.add_mul, one_mul] at this; omega
        · intro p₁ hp₁ p₂ hp₂ heq
          simp only [Finset.mem_product, Finset.mem_range] at hp₁ hp₂
          have h1 : (p₁.1 * L + p₁.2) / L = p₁.1 := by
            rw [Nat.mul_comm p₁.1 L, Nat.mul_add_div hL_pos, Nat.div_eq_of_lt hp₁.2, add_zero]
          have h2 : (p₂.1 * L + p₂.2) / L = p₂.1 := by
            rw [Nat.mul_comm p₂.1 L, Nat.mul_add_div hL_pos, Nat.div_eq_of_lt hp₂.2, add_zero]
          have hfst : p₁.1 = p₂.1 := by rw [← h1, heq, h2]
          ext
          · exact hfst
          · rw [hfst] at heq; omega
        · intro a ha
          simp only [Finset.mem_range] at ha
          refine ⟨(a / L, a % L), ?_, Nat.div_add_mod' a L⟩
          simp only [Finset.mem_product, Finset.mem_range]
          exact ⟨(Nat.div_lt_iff_lt_mul hL_pos).mpr ha, Nat.mod_lt a hL_pos⟩
      rw [heq, Finset.sum_product]
    rw [hsplit]
    have hcycle : ∀ k ∈ Finset.range q, ∑ j ∈ Finset.range L,
        (if (z.val + N - (rowMap N t hN (k * L + j)).val) % N < t then 1 else 0) = t / d0 := by
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [← Finset.card_filter]
      set S := (Finset.range t).filter (fun v => (z.val + N - v) % d0 = k)
      have hcard_S : S.card = t / d0 := by
        set w := (z.val + N - k) % d0
        have hw : w < d0 := Nat.mod_lt _ hd0_pos
        have hS_eq : S = (Finset.range t).filter (fun v => v % d0 = w) := by
          ext v
          simp only [S, Finset.mem_filter, Finset.mem_range]
          refine and_congr_right (fun hv => ?_)
          have hvt : v < N := by omega
          have hkt : k < d0 := by omega
          constructor
          · intro h
            have h1 : (z.val + N - v + v) % d0 = (k + v) % d0 :=
              mod_add_left_eq _ _ _ _ (by rw [h, Nat.mod_eq_of_lt hkt])
            have h2 : z.val + N - v + v = z.val + N := by omega
            rw [h2] at h1
            have h3 : (k + v + (d0 - k)) % d0 = (z.val + N + (d0 - k)) % d0 :=
              mod_add_left_eq _ _ _ _ h1.symm
            have h4 : k + v + (d0 - k) = v + d0 := by omega
            have h5 : z.val + N + (d0 - k) = (z.val + N - k) + d0 := by omega
            rw [h4, Nat.add_mod_right, h5, Nat.add_mod_right] at h3
            exact h3
          · intro h
            have h1 : (v + (z.val + N - v)) % d0 = (w + (z.val + N - v)) % d0 :=
              mod_add_left_eq _ _ _ _ (by rw [h, Nat.mod_eq_of_lt hw])
            have h2 : v + (z.val + N - v) = z.val + N := by omega
            rw [h2] at h1
            have h3 : (z.val + N - v + w) % d0 = (z.val + N) % d0 := by
              rw [Nat.add_comm]; exact h1.symm
            have h4 : (z.val + N - v + (z.val + N - k)) % d0 = (z.val + N) % d0 := by
              rw [Nat.add_mod, show (z.val + N - k) % d0 = w % d0 from (Nat.mod_eq_of_lt hw).symm,
                ← Nat.add_mod]
              exact h3
            have h5 : (z.val + N - v + (z.val + N - k) + k) % d0 = (z.val + N + k) % d0 := by
              rw [Nat.add_mod (z.val + N - v + _), h4, ← Nat.add_mod]
            have h6 : z.val + N - v + (z.val + N - k) + k = (z.val + N - v) + (z.val + N) := by omega
            rw [h6] at h5
            have h7 : ((z.val + N - v) % d0 + (z.val + N) % d0) % d0 =
                (k % d0 + (z.val + N) % d0) % d0 := by
              rw [← Nat.add_mod, ← Nat.add_mod, Nat.add_comm k]; exact h5
            set c := (z.val + N) % d0
            have hc : c < d0 := Nat.mod_lt _ hd0_pos
            have hl1 : (z.val + N - v) % d0 < d0 := Nat.mod_lt _ hd0_pos
            rw [Nat.mod_eq_of_lt hkt] at h7
            by_cases ha : (z.val + N - v) % d0 + c < d0 <;> by_cases hb : k + c < d0
            · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h7; omega
            · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_sub_mod (by omega : d0 ≤ k + c),
                Nat.mod_eq_of_lt (by omega : k + c - d0 < d0)] at h7; omega
            · rw [Nat.mod_eq_sub_mod (by omega : d0 ≤ (z.val + N - v) % d0 + c),
                Nat.mod_eq_of_lt (by omega : (z.val + N - v) % d0 + c - d0 < d0),
                Nat.mod_eq_of_lt hb] at h7; omega
            · rw [Nat.mod_eq_sub_mod (by omega : d0 ≤ (z.val + N - v) % d0 + c),
                Nat.mod_eq_of_lt (by omega : (z.val + N - v) % d0 + c - d0 < d0),
                Nat.mod_eq_sub_mod (by omega : d0 ≤ k + c),
                Nat.mod_eq_of_lt (by omega : k + c - d0 < d0)] at h7; omega
        rw [hS_eq, count_mod_in_range d0 t w hd0_pos hw]
        rw [Nat.dvd_iff_mod_eq_zero.mp hd0_t]; simp
      rw [← hcard_S]
      refine Finset.card_bij (fun j _ => (z.val + N - (rowMap N t hN (k * L + j)).val) % N) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp only [S, Finset.mem_filter, Finset.mem_range]
        refine ⟨hj.2, ?_⟩
        set x := (rowMap N t hN (k * L + j)).val
        have hx_lt : x < N := (rowMap N t hN (k * L + j)).isLt
        have hx_d0 : x % d0 = k := by
          simp only [x, rowMap]
          change ((k * L + j) / L + (k * L + j) % L * t) % N % d0 = k
          rw [Nat.mod_mod_of_dvd _ hd0_N,
            Nat.mul_comm k L, Nat.mul_add_div hL_pos, Nat.div_eq_of_lt hj.1, add_zero,
            Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hj.1,
            Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_of_dvd_right hd0_t j), add_zero,
            Nat.mod_mod, Nat.mod_eq_of_lt (by omega : k < d0)]
        have hv_lt : (z.val + N - x) % N < N := Nat.mod_lt _ hN
        have h1 : (z.val + N - (z.val + N - x) % N) % N = x := by
          by_cases hzx : x ≤ z.val
          · have h2 : z.val + N - x = (z.val - x) + N := by omega
            rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x < N)]
            have h3 : z.val + N - (z.val - x) = x + N := by omega
            rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt hx_lt]
          · have h2 : z.val + N - x < N := by omega
            rw [Nat.mod_eq_of_lt h2]
            have h3 : z.val + N - (z.val + N - x) = x := by omega
            rw [h3, Nat.mod_eq_of_lt hx_lt]
        rw [← Nat.mod_mod_of_dvd _ hd0_N, h1, hx_d0]
      · intro j₁ hj₁ j₂ hj₂ heq
        simp only [Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
        have hx_eq : (rowMap N t hN (k * L + j₁)) = (rowMap N t hN (k * L + j₂)) := by
          apply Fin.ext
          set x₁ := (rowMap N t hN (k * L + j₁)).val
          set x₂ := (rowMap N t hN (k * L + j₂)).val
          have hx1 := (rowMap N t hN (k * L + j₁)).isLt
          have hx2 := (rowMap N t hN (k * L + j₂)).isLt
          have h1 : ∀ x < N, (z.val + N - (z.val + N - x) % N) % N = x := by
            intro x hx
            by_cases hzx : x ≤ z.val
            · have e1 : z.val + N - x = (z.val - x) + N := by omega
              rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - x < N)]
              have e2 : z.val + N - (z.val - x) = x + N := by omega
              rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
            · rw [Nat.mod_eq_of_lt (by omega : z.val + N - x < N)]
              have e2 : z.val + N - (z.val + N - x) = x := by omega
              rw [e2, Nat.mod_eq_of_lt hx]
          rw [← h1 x₁ hx1, heq, h1 x₂ hx2]
        have hlt1 : k * L + j₁ < r := by
          have : (k + 1) * L ≤ q * L := Nat.mul_le_mul_right L (by omega)
          rw [Nat.add_mul, one_mul] at this; omega
        have hlt2 : k * L + j₂ < r := by
          have : (k + 1) * L ≤ q * L := Nat.mul_le_mul_right L (by omega)
          rw [Nat.add_mul, one_mul] at this; omega
        have ha_eq := rowMap_inj hN hr _ (Finset.mem_range.mpr hlt1) _ (Finset.mem_range.mpr hlt2) hx_eq
        omega
      · intro v hv
        simp only [S, Finset.mem_filter, Finset.mem_range] at hv
        set x := (z.val + N - v) % N
        have hx_lt : x < N := Nat.mod_lt _ hN
        have hx_d0 : x % d0 = k := by
          rw [Nat.mod_mod_of_dvd _ hd0_N]; exact hv.2

        have hcop : Nat.Coprime (t / d0) L := by
          have := (Nat.coprime_div_gcd_div_gcd hd0_pos (m := N) (n := t)).symm
          simpa [L, d0] using this
        have hkx : k ≤ x := by
          have := Nat.div_add_mod x d0; omega
        set diff := (x - k) / d0
        have hdiff_eq : diff * d0 = x - k := by
          apply Nat.div_mul_cancel
          rw [Nat.dvd_iff_mod_eq_zero]
          have h1 := Nat.div_add_mod x d0
          have h2 : x - k = d0 * (x / d0) := by omega
          rw [h2, Nat.mul_mod_right]
        have hex_j : ∃ j < L, (j * (t / d0)) % L = diff % L := by
          let g : Fin L → Fin L := fun j => ⟨(j.val * (t / d0)) % L, Nat.mod_lt _ hL_pos⟩
          have hginj : Function.Injective g := by
            intro j₁ j₂ h
            have hgv := congrArg Fin.val h
            simp only [g] at hgv
            apply Fin.ext
            rcases le_total j₁.val j₂.val with hle | hle
            · have hdvd : L ∣ (j₂.val - j₁.val) * (t / d0) := by
                rw [Nat.sub_mul]
                exact (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right _ hle)).mp hgv
              have hdvd' : L ∣ j₂.val - j₁.val := hcop.symm.dvd_of_dvd_mul_right hdvd
              have : j₂.val - j₁.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
              omega
            · have hdvd : L ∣ (j₁.val - j₂.val) * (t / d0) := by
                rw [Nat.sub_mul]
                exact (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right _ hle)).mp hgv.symm
              have hdvd' : L ∣ j₁.val - j₂.val := hcop.symm.dvd_of_dvd_mul_right hdvd
              have : j₁.val - j₂.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
              omega
          have hgsurj : Function.Surjective g := Finite.injective_iff_surjective.mp hginj
          obtain ⟨j, hj⟩ := hgsurj ⟨diff % L, Nat.mod_lt _ hL_pos⟩
          exact ⟨j.val, j.isLt, congrArg Fin.val hj⟩
        rcases hex_j with ⟨j, hjL, hjmod⟩
        have hrm : (rowMap N t hN (k * L + j)).val = x := by
          simp only [rowMap]
          change ((k * L + j) / L + (k * L + j) % L * t) % N = x
          rw [Nat.mul_comm k L, Nat.mul_add_div hL_pos, Nat.div_eq_of_lt hjL, add_zero,
            Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hjL]
          have hteq : t = (t / d0) * d0 := (Nat.div_mul_cancel hd0_t).symm
          have hmul_mod : (j * t) % N = (x - k) % N := by
            rw [hteq, ← Nat.mul_assoc, ← hLd0, Nat.mul_mod_mul_right, hjmod,
              ← Nat.mul_mod_mul_right, hdiff_eq]
          rw [Nat.add_mod, hmul_mod, ← Nat.add_mod, Nat.add_sub_of_le hkx, Nat.mod_eq_of_lt hx_lt]
        have hzv : (z.val + N - x) % N = v := by
          by_cases hzv' : v ≤ z.val
          · have e1 : z.val + N - v = (z.val - v) + N := by omega
            have hx_eq : x = z.val - v := by
              simp only [x, e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : z.val - v < N)]
            rw [hx_eq]
            have e2 : z.val + N - (z.val - v) = v + N := by omega
            rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : v < N)]
          · have hx_eq : x = z.val + N - v := by
              simp only [x, Nat.mod_eq_of_lt (by omega : z.val + N - v < N)]
            rw [hx_eq]
            have e2 : z.val + N - (z.val + N - v) = v := by omega
            rw [e2, Nat.mod_eq_of_lt (by omega : v < N)]
        exact ⟨j, by simp [hjL, hrm, hzv, hv.1], by rw [hrm, hzv]⟩
    rw [Finset.sum_congr rfl hcycle, Finset.sum_const, Finset.card_range, smul_eq_mul]

  have hpart : ∑ a ∈ Finset.Ico (q * L) (q * L + m),
      (if (z.val + N - (rowMap N t hN a).val) % N < t then 1 else 0) =
      (m * t) / N + (if (z.val + N - q) % N < (m * t) % N then 1 else 0) := by
    set w := (z.val + N - q) % N
    have hw : w < N := Nat.mod_lt _ hN
    have hshift : ∑ a ∈ Finset.Ico (q * L) (q * L + m),
        (if (z.val + N - (rowMap N t hN a).val) % N < t then 1 else 0) =
        ∑ j ∈ Finset.range m, (if (w + N - (j * t) % N) % N < t then 1 else 0) := by
      refine Finset.sum_bij (fun a _ => a - q * L) ?_ ?_ ?_ ?_
      · intro a ha; simp at ha ⊢; omega
      · intro a₁ ha₁ a₂ ha₂ heq; simp at ha₁ ha₂; omega
      · intro j hj; simp at hj
        exact ⟨q * L + j, by simp [hj], by omega⟩
      · intro a ha
        simp only [Finset.mem_Ico] at ha
        set j := a - q * L
        have hm_lt : m < L := Nat.mod_lt r hL_pos
        have hj : j < L := by omega
        have ha_eq : a = q * L + j := by omega
        have hrm : (rowMap N t hN a).val = (q + (j * t) % N) % N := by
          simp only [rowMap, ha_eq]
          change ((q * L + j) / L + (q * L + j) % L * t) % N = (q + (j * t) % N) % N
          rw [Nat.mul_comm q L, Nat.mul_add_div hL_pos, Nat.div_eq_of_lt hj, add_zero,
            Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hj,
            Nat.add_mod, Nat.add_mod q, Nat.mod_mod]
        have hmod_eq : (z.val + N - (rowMap N t hN a).val) % N = (w + N - (j * t) % N) % N := by
          rw [hrm]
          set b := (j * t) % N
          have hb : b < N := Nat.mod_lt _ hN
          have hz : z.val < N := z.isLt
          have h1 : (z.val + N - (q + b) % N) % N = (z.val + 2 * N - q - b) % N := by
            by_cases hqb : q + b < N
            · rw [Nat.mod_eq_of_lt hqb]
              have : z.val + 2 * N - q - b = (z.val + N - (q + b)) + N := by omega
              rw [this, Nat.add_mod_right]
            · rw [Nat.mod_eq_sub_mod (by omega : N ≤ q + b),
                Nat.mod_eq_of_lt (by omega : q + b - N < N)]
              have : z.val + N - (q + b - N) = z.val + 2 * N - q - b := by omega
              rw [this]
          have h2 : (w + N - b) % N = (z.val + 2 * N - q - b) % N := by
            by_cases hzq : q ≤ z.val
            · have hw_eq : w = z.val - q := by
                simp only [w]
                have : z.val + N - q = (z.val - q) + N := by omega
                have hlt : z.val - q < N := lt_of_le_of_lt (Nat.sub_le _ _) hz
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
              rw [hw_eq]
              have : z.val + 2 * N - q - b = (z.val - q + N - b) + N := by omega
              rw [this, Nat.add_mod_right]
            · have hw_eq : w = z.val + N - q := by
                simp only [w]
                have hlt : z.val + N - q < N := by omega
                exact Nat.mod_eq_of_lt hlt
              rw [hw_eq]
              have : z.val + N - q + N - b = z.val + 2 * N - q - b := by omega
              rw [this]
          rw [h1, h2]
        rw [hmod_eq]
    rw [hshift]
    have hblocks : ∑ j ∈ Finset.range m, (if (w + N - (j * t) % N) % N < t then 1 else 0) =
        ∑ j ∈ Finset.range m, ((Finset.Ico (j * t) ((j + 1) * t)).filter (fun v => v % N = w)).card := by
      apply Finset.sum_congr rfl
      intro j _
      exact (count_mod_in_block N t j w hN ht hw).symm
    rw [hblocks, ← count_mod_in_range N (m * t) w hN hw]

    have hbiUnion : (Finset.range (m * t)).filter (fun v => v % N = w) =
        (Finset.range m).biUnion (fun j => (Finset.Ico (j * t) ((j + 1) * t)).filter (fun v => v % N = w)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_Ico]
      constructor
      · rintro ⟨hv, hmod⟩
        have ht_pos : 0 < t := by
          by_contra h; push_neg at h; interval_cases t; simp at hv
        refine ⟨v / t, (Nat.div_lt_iff_lt_mul ht_pos).mpr hv, ⟨?_, ?_⟩, hmod⟩
        · exact Nat.div_mul_le_self v t
        · rw [Nat.add_mul, one_mul]
          have := Nat.div_add_mod' v t
          have := Nat.mod_lt v ht_pos
          omega
      · rintro ⟨j, hj, ⟨_, hv2⟩, hmod⟩
        refine ⟨?_, hmod⟩
        have : (j + 1) * t ≤ m * t := Nat.mul_le_mul_right t (by omega)
        omega
    rw [hbiUnion, Finset.card_biUnion]
    intro j₁ _ j₂ _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_filter, Finset.mem_Ico] at hv1 hv2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (j₁ + 1) * t ≤ j₂ * t := Nat.mul_le_mul_right t (by omega)
      omega
    · have : (j₂ + 1) * t ≤ j₁ * t := Nat.mul_le_mul_right t (by omega)
      omega
  rw [hfull, hpart]
  have hqLt : q * L * t = (q * (t / d0)) * N := by
    have hteq : t = (t / d0) * d0 := (Nat.div_mul_cancel hd0_t).symm
    calc q * L * t = q * L * ((t / d0) * d0) := by congr 1
      _ = (q * (t / d0)) * (L * d0) := by ring
      _ = (q * (t / d0)) * N := by rw [hLd0]
  have hrt : r * t = N * (q * (t / d0)) + m * t := by
    rw [hr_eq, Nat.add_mul, hqLt, Nat.mul_comm]
  rw [hrt, Nat.mul_add_div hN, Nat.mul_add_mod_self_left]
  omega

lemma floor_diff_mod (N s k : ℕ) (hN : 0 < N) :
    ((k + 1) * s) / N - (k * s) / N = ((k % N + 1) * s) / N - ((k % N) * s) / N := by
  have hk := Nat.div_add_mod k N
  have h1 : k * s = N * ((k / N) * s) + (k % N) * s := by
    calc k * s = (N * (k / N) + k % N) * s := by rw [hk]
      _ = N * ((k / N) * s) + (k % N) * s := by ring
  have h2 : (k + 1) * s = N * ((k / N) * s) + (k % N + 1) * s := by
    calc (k + 1) * s = (N * (k / N) + (k % N + 1)) * s := by rw [← Nat.add_assoc, hk]
      _ = N * ((k / N) * s) + (k % N + 1) * s := by ring
  rw [h1, h2, Nat.mul_add_div hN, Nat.mul_add_div hN]
  omega

lemma sum_floor_diff_Ico (N s a b : ℕ) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (((k + 1) * s) / N - (k * s) / N) = (b * s) / N - (a * s) / N := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; simp
  | succ m ih =>
    by_cases h : a ≤ m
    · rw [Finset.sum_Ico_succ_top h, ih h]
      have h1 : (a * s) / N ≤ (m * s) / N := Nat.div_le_div_right (Nat.mul_le_mul_right s h)
      have h2 : (m * s) / N ≤ ((m + 1) * s) / N := Nat.div_le_div_right (Nat.mul_le_mul_right s (by omega))
      omega
    · have : a = m + 1 := by omega
      subst this; simp

lemma sum_floor_shift (N s B : ℕ) (hN : 0 < N) :
    ∑ a ∈ Finset.range N, (((a + B) * s) / N - (a * s) / N) = B * s := by
  induction B with
  | zero => simp
  | succ m ih =>
    have hstep : ∀ a ∈ Finset.range N,
        ((a + (m + 1)) * s) / N - (a * s) / N =
        (((a + m) * s) / N - (a * s) / N) +
          ((((a + m) + 1) * s) / N - ((a + m) * s) / N) := by
      intro a _
      have h1 : (a * s) / N ≤ ((a + m) * s) / N := Nat.div_le_div_right (Nat.mul_le_mul_right s (by omega))
      have h2 : ((a + m) * s) / N ≤ (((a + m) + 1) * s) / N :=
        Nat.div_le_div_right (Nat.mul_le_mul_right s (by omega))
      rw [show a + (m + 1) = (a + m) + 1 by omega]
      omega
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ih]
    have htele : ∑ a ∈ Finset.range N, ((((a + m) + 1) * s) / N - ((a + m) * s) / N) = s := by
      have hbij : ∑ a ∈ Finset.range N, ((((a + m) + 1) * s) / N - ((a + m) * s) / N) =
          ∑ k ∈ Finset.Ico m (m + N), (((k + 1) * s) / N - (k * s) / N) := by
        refine Finset.sum_bij (fun a _ => a + m) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro a ha; simp at ha ⊢; omega
        · intro a₁ _ a₂ _ h; omega
        · intro k hk; simp at hk; exact ⟨k - m, by simp; omega, by omega⟩
      rw [hbij, sum_floor_diff_Ico N s m (m + N) (by omega)]
      have h1 : (m + N) * s = m * s + s * N := by ring
      rw [h1, Nat.add_mul_div_right _ _ hN]
      omega
    rw [htele, Nat.add_mul, one_mul]

lemma floor_diff_le_ceil (N s a B : ℕ) (hN : 0 < N) :
    ((a + B) * s) / N - (a * s) / N ≤ (B * s + N - 1) / N := by
  have h1 : (a + B) * s = a * s + B * s := Nat.add_mul a B s
  have ha := Nat.div_add_mod (a * s) N
  have ha_lt := Nat.mod_lt (a * s) hN
  have h2 : (a + B) * s = N * ((a * s) / N) + ((a * s) % N + B * s) := by omega
  rw [h2, Nat.mul_add_div hN, Nat.add_sub_cancel_left]
  exact Nat.div_le_div_right (by omega)

end PEqualNP.Outside.L_meta_32586

open PEqualNP.Outside.L_meta_32586 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_32586 : (∀ (N g t d r s : ℕ), 0 < g → 2*g+1 < N → N < 2*t → t ≤ N →
  r+s=g+1 → 0 < d → d ≤ r*s → r*s < N →
  (∀ i : ℕ, i ≤ g+1 → d ≤ i*(g+1-i) → r*s ≤ i*(g+1-i)) →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let area := fun (C : Circ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 = true)).card
  let loss := fun (C : Circ) (u : ℕ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 ≠
      decide ((z.2.val + N - z.1.val + N - u % N) % N < t))).card
  let p := r*s
  let A := (g+1)*N-p
  let bench := N*(N*t)-(2*t-N)*A
  let fits := fun (C : Circ) => legal C ∧ C.size ≤ g ∧ area C ≤ (g+1)*N-d
  let total := fun (M : ℕ) (D : Fin M → Circ) (u : X) => ∑ i, loss (D i) u.val
  (∃ D : ℕ → Circ, (∀ i, fits (D i) ∧ area (D i) = A ∧ D (i+N) = D i) ∧
    (∀ (i : ℕ) (x y z : X), z.val = (y.val+i*r*t) % N →
      table (D i) x y = table (D 0) x z) ∧
    ∀ M : ℕ, 0 < M →
      (Finset.univ.sup (fun u : X => N*total M (fun i => D i.val) u)) =
        M*bench + 2*(N*((M*p*t+N-1)/N)-M*p*t)) ∧
  ∀ M : ℕ, 0 < M →
    (∀ D : Fin M → Circ, (∀ i, fits (D i)) →
      ∃ u : X, M*bench ≤ N*total M D u) ∧
    ((∃ D : Fin M → Circ, (∀ i, fits (D i)) ∧
      ∀ u : X, N*total M D u ≤ M*bench) ↔ N ∣ M*p*t)) := by
  intro N g t d r s hg hN_gt hNt ht hrs hd0 hdrs hrsN hmin
  intro X Circ legal table area loss p A bench fits total
  have hN : 0 < N := by omega
  have hr_pos : 0 < r := by
    by_contra h; push_neg at h; interval_cases r; simp at hdrs; omega
  have hs_pos : 0 < s := by
    by_contra h; push_neg at h; interval_cases s; simp at hdrs; omega
  have hr_lt : r < N := by omega
  have hs_lt : s < N := by omega
  have hp_le_gN : p ≤ (g + 1) * N := by
    have : 1 * N ≤ (g + 1) * N := Nat.mul_le_mul_right N (by omega)
    omega
  have h2tN_A : (2 * t - N) * A ≤ N * (N * t) := by
    have h1 : A ≤ (g + 1) * N := Nat.sub_le _ _
    have h2 : (2 * t - N) * A ≤ N * A := Nat.mul_le_mul_right A (by omega)
    have h3 : (2 * t - N) * A ≤ (2 * t - N) * ((g + 1) * N) := Nat.mul_le_mul_left _ h1

    have h4 : (2 * t - N) * (g + 1) ≤ N * t := by
      have h2g : 2 * (g + 1) ≤ N := by omega
      calc (2 * t - N) * (g + 1) ≤ t * (g + 1) := Nat.mul_le_mul_right _ (by omega)
        _ ≤ t * N := Nat.mul_le_mul_left _ (by omega)
        _ = N * t := Nat.mul_comm _ _
    calc (2 * t - N) * A ≤ (2 * t - N) * ((g + 1) * N) := h3
      _ = ((2 * t - N) * (g + 1)) * N := by ring
      _ ≤ (N * t) * N := Nat.mul_le_mul_right N h4
      _ = N * (N * t) := by ring

  set R0 : Finset (Fin N) := (Finset.range r).image (rowMap N t hN)
  have hR0_card : R0.card = r := by
    rw [Finset.card_image_of_injOn (rowMap_inj hN hr_lt), Finset.card_range]
  set C0 : Finset (Fin N) :=
    Finset.univ.filter (fun c : Fin N => (c.val * s) / N < ((c.val + 1) * s) / N)
  have hC0_step : ∀ c : ℕ, ((c + 1) * s) / N - (c * s) / N =
      if (c * s) / N < ((c + 1) * s) / N then 1 else 0 := by
    intro c
    have hle : (c * s) / N ≤ ((c + 1) * s) / N :=
      Nat.div_le_div_right (Nat.mul_le_mul_right s (by omega))
    have hhi : ((c + 1) * s) / N ≤ (c * s) / N + 1 := by
      have : (c + 1) * s ≤ c * s + N := by rw [Nat.add_mul, one_mul]; omega
      calc ((c + 1) * s) / N ≤ (c * s + N) / N := Nat.div_le_div_right this
        _ = (c * s) / N + 1 := Nat.add_div_right _ hN
    split_ifs <;> omega
  have hC0_card : C0.card = s := by
    rw [Finset.card_filter]
    have hsum : ∑ c : Fin N, (if (c.val * s) / N < ((c.val + 1) * s) / N then 1 else 0) =
        ∑ k ∈ Finset.range N, (((k + 1) * s) / N - (k * s) / N) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => if (k * s) / N < ((k + 1) * s) / N then 1 else 0)]
      exact Finset.sum_congr rfl (fun k _ => (hC0_step k).symm)
    rw [hsum, show Finset.range N = Finset.Ico 0 N from (Nat.Ico_zero_eq_range N).symm,
      sum_floor_diff_Ico N s 0 N (by omega)]
    simp [Nat.mul_div_cancel_left s hN]
  let shiftY (i : ℕ) (y : Fin N) : Fin N := ⟨(y.val + (i % N) * r * t) % N, Nat.mod_lt _ hN⟩
  have hshiftY_bij : ∀ i : ℕ, Function.Bijective (shiftY i) := by
    intro i
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro y₁ y₂ h
    have hv := congrArg Fin.val h
    simp only [shiftY] at hv
    set c := ((i % N) * r * t) % N
    have hc : c < N := Nat.mod_lt _ hN
    have h1 : (y₁.val + (i % N) * r * t) % N = (y₁.val + c) % N := by
      rw [Nat.add_mod, Nat.add_mod y₁.val, Nat.mod_mod]
    have h2 : (y₂.val + (i % N) * r * t) % N = (y₂.val + c) % N := by
      rw [Nat.add_mod, Nat.add_mod y₂.val, Nat.mod_mod]
    rw [h1, h2] at hv
    have hy1 := y₁.isLt; have hy2 := y₂.isLt
    apply Fin.ext
    by_cases ha : y₁.val + c < N <;> by_cases hb : y₂.val + c < N
    · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv; omega
    · rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at hv; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt hb] at hv; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
  let Ci (i : ℕ) : Finset (Fin N) := Finset.univ.filter (fun y => shiftY i y ∈ C0)
  have hCi_card : ∀ i, (Ci i).card = s := by
    intro i
    rw [← hC0_card]
    refine Finset.card_bij (fun y _ => shiftY i y) (fun y hy => by simpa [Ci] using hy)
      (fun a _ b _ h => (hshiftY_bij i).1 h) (fun c hc => ?_)
    obtain ⟨y, hy⟩ := (hshiftY_bij i).2 c
    exact ⟨y, by simpa [Ci, hy] using hc, hy⟩
  let wireSet (i : ℕ) : Finset ℕ :=
    R0.image Fin.val ∪ (Ci i).image (fun y => N + y.val)
  have hwireSet_card : ∀ i, (wireSet i).card = g + 1 := by
    intro i
    have hdisj : Disjoint (R0.image Fin.val) ((Ci i).image (fun y => N + y.val)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rcases Finset.mem_image.mp hw1 with ⟨x, _, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨y, _, hy⟩
      omega
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega)),
      hR0_card, hCi_card i, hrs]
  have hwireSet_lt : ∀ i w, w ∈ wireSet i → w < N + N := by
    intro i w hw
    rcases Finset.mem_union.mp hw with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨x, _, rfl⟩; omega
    · rcases Finset.mem_image.mp h2 with ⟨y, _, rfl⟩; omega
  let D : ℕ → Circ := fun i =>
    match (wireSet i).sort (· ≤ ·) with
    | [] => ⟨[], 0⟩
    | w0 :: ws => orChain (N + N) w0 ws
  have hD_table : ∀ i (x y : Fin N), table (D i) x y = decide (x ∈ R0 ∨ y ∈ Ci i) := by
    intro i x y
    have hlen : ((wireSet i).sort (· ≤ ·)).length = g + 1 := by
      rw [Finset.length_sort, hwireSet_card i]
    cases hsort : (wireSet i).sort (· ≤ ·) with
    | nil => rw [hsort] at hlen; simp at hlen
    | cons w0 ws =>
      have hw0_lt : w0 < N + N := hwireSet_lt i w0 ((Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; simp))
      have hws_lt : ∀ w ∈ ws, w < N + N := fun w hw =>
        hwireSet_lt i w ((Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; simp [hw]))
      simp only [table, D, hsort]
      rw [orChain_eval (N + N) w0 ws hw0_lt hws_lt (oneEach x y) (oneEach_length x y)]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨w, hw, hwt⟩
        have hw_mem : w ∈ wireSet i := (Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; exact hw)
        rcases Finset.mem_union.mp hw_mem with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨x', hx', rfl⟩
          rw [oneEach_getD_left x y x'.val x'.isLt] at hwt
          exact Or.inl (by rwa [← Fin.ext (of_decide_eq_true hwt)])
        · rcases Finset.mem_image.mp h2 with ⟨y', hy', rfl⟩
          rw [oneEach_getD_right x y y'.val y'.isLt] at hwt
          exact Or.inr (by rwa [← Fin.ext (of_decide_eq_true hwt)])
      · rintro (hx | hy)
        · refine ⟨x.val, ?_, ?_⟩
          · have : x.val ∈ (wireSet i).sort (· ≤ ·) :=
              (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
            rwa [hsort] at this
          · rw [oneEach_getD_left x y x.val x.isLt]; simp
        · refine ⟨N + y.val, ?_, ?_⟩
          · have : N + y.val ∈ (wireSet i).sort (· ≤ ·) :=
              (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
            rwa [hsort] at this
          · rw [oneEach_getD_right x y y.val y.isLt]; simp
  have hD_area : ∀ i, area (D i) = A := by
    intro i
    have hfilt : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => table (D i) z.1 z.2 = true) =
        (R0 ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ Ci i) := by
      ext z; simp [hD_table]
    have hinter : (R0 ×ˢ (Finset.univ : Finset (Fin N))) ∩ (Finset.univ ×ˢ Ci i) = R0 ×ˢ Ci i := by
      ext z; simp
    have hinc := Finset.card_union_add_card_inter (R0 ×ˢ (Finset.univ : Finset (Fin N)))
      ((Finset.univ : Finset (Fin N)) ×ˢ Ci i)
    rw [← hfilt, hinter, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_univ, Fintype.card_fin, hR0_card, hCi_card i] at hinc
    change ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => table (D i) z.1 z.2 = true)).card =
      (g + 1) * N - r * s
    have : (g + 1) * N = r * N + N * s := by rw [← hrs]; ring
    omega
  have hD_fits : ∀ i, fits (D i) := by
    intro i
    have hlen : ((wireSet i).sort (· ≤ ·)).length = g + 1 := by
      rw [Finset.length_sort, hwireSet_card i]
    cases hsort : (wireSet i).sort (· ≤ ·) with
    | nil => rw [hsort] at hlen; simp at hlen
    | cons w0 ws =>
      have hw0_lt : w0 < N + N := hwireSet_lt i w0 ((Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; simp))
      have hws_lt : ∀ w ∈ ws, w < N + N := fun w hw =>
        hwireSet_lt i w ((Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; simp [hw]))
      have hws_len : ws.length = g := by rw [hsort] at hlen; simp at hlen; omega
      refine ⟨?_, ?_, ?_⟩
      · simpa [D, hsort, legal] using orChain_legal N w0 ws hw0_lt hws_lt
      · simpa [D, hsort, orChain_size] using le_of_eq hws_len
      · rw [hD_area i]; omega
  have hD_per : ∀ i, D (i + N) = D i := by
    intro i
    have hci : Ci (i + N) = Ci i := by
      ext y; simp [Ci, shiftY, Nat.add_mod_right]
    simp [D, wireSet, hci]
  have hD_shift : ∀ (i : ℕ) (x y z : X), z.val = (y.val + i * r * t) % N →
      table (D i) x y = table (D 0) x z := by
    intro i x y z hz
    rw [hD_table i x y, hD_table 0 x z]
    congr 1
    have hyz : shiftY i y = shiftY 0 z := by
      apply Fin.ext
      simp only [shiftY, Nat.zero_mod, zero_mul, add_zero, hz]
      have hmul_eq : ((i % N) * r * t) % N = (i * r * t) % N := by
        rw [Nat.mul_assoc (i % N), Nat.mul_assoc i, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [Nat.mod_mod]
      exact mod_add_right_eq _ _ _ _ hmul_eq
    simp [Ci, hyz]

  have hD_sup : ∀ M : ℕ, 0 < M →
      (Finset.univ.sup (fun u : X => N * total M (fun i => D i.val) u)) =
        M * bench + 2 * (N * ((M * p * t + N - 1) / N) - M * p * t) := by
    intro M hM
    set d0 := Nat.gcd N t
    set L := N / d0
    set q0 := r / L
    set l := (r * t) % N
    have hd0_pos : 0 < d0 := Nat.gcd_pos_of_pos_left t hN
    have hLd0 : L * d0 = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N t)
    have hL_pos : 0 < L := by
      by_contra h; push_neg at h; interval_cases L; simp at hLd0; omega
    have hq0_lt : q0 < N := by
      have : q0 ≤ r := Nat.div_le_self r L; omega

    let K (i : ℕ) (u : X) : ℕ :=
      ((Finset.univ : Finset (X × X)).filter
        (fun z => z.1 ∈ R0 ∧ z.2 ∈ Ci i ∧ targetI N t u.val z.1 z.2 = true)).card
    have hloss_K : ∀ (i : ℕ) (u : X),
        loss (D i) u.val + 2 * (g + 1) * t = A + N * t + 2 * K i u := by
      intro i u
      have h1 := loss_add_two_overlap ht (fun z => table (D i) z.1 z.2) u.val
      change loss (D i) u.val + 2 * _ = area (D i) + N * t at h1
      rw [hD_area i] at h1

      have hov : ((Finset.univ : Finset (X × X)).filter
            (fun z => table (D i) z.1 z.2 = true ∧ targetI N t u.val z.1 z.2 = true)).card +
          K i u = (g + 1) * t := by
        set SR_I := (Finset.univ : Finset (X × X)).filter
          (fun z => z.1 ∈ R0 ∧ targetI N t u.val z.1 z.2 = true)
        set SC_I := (Finset.univ : Finset (X × X)).filter
          (fun z => z.2 ∈ Ci i ∧ targetI N t u.val z.1 z.2 = true)
        have hunion : SR_I ∪ SC_I = (Finset.univ : Finset (X × X)).filter
            (fun z => table (D i) z.1 z.2 = true ∧ targetI N t u.val z.1 z.2 = true) := by
          ext z; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
            SR_I, SC_I, hD_table, decide_eq_true_eq]; tauto
        have hinter : SR_I ∩ SC_I = (Finset.univ : Finset (X × X)).filter
            (fun z => z.1 ∈ R0 ∧ z.2 ∈ Ci i ∧ targetI N t u.val z.1 z.2 = true) := by
          ext z; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
            SR_I, SC_I]; tauto
        have hSR_I : SR_I.card = r * t := by
          rw [Finset.card_filter, Fintype.sum_prod_type]
          have hfx : ∀ x : Fin N, ∑ y : Fin N,
              (if x ∈ R0 ∧ targetI N t u.val x y = true then 1 else 0) =
              if x ∈ R0 then t else 0 := by
            intro x
            by_cases hx : x ∈ R0
            · simp only [hx, true_and, ↓reduceIte]
              rw [← Finset.card_filter]; exact card_targetI_col ht u.val x
            · simp [hx]
          rw [Finset.sum_congr rfl (fun x _ => hfx x),
            Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, hR0_card]
        have hSC_I : SC_I.card = s * t := by
          rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
          have hfy : ∀ y : Fin N, ∑ x : Fin N,
              (if y ∈ Ci i ∧ targetI N t u.val x y = true then 1 else 0) =
              if y ∈ Ci i then t else 0 := by
            intro y
            by_cases hy : y ∈ Ci i
            · simp only [hy, true_and, ↓reduceIte]
              rw [← Finset.card_filter]; exact card_targetI_row ht u.val y
            · simp [hy]
          rw [Finset.sum_congr rfl (fun y _ => hfy y),
            Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, hCi_card i]
        have hinc := Finset.card_union_add_card_inter SR_I SC_I
        rw [hunion, hinter, hSR_I, hSC_I] at hinc
        change _ + K i u = r * t + s * t at hinc
        rw [← Nat.add_mul, hrs] at hinc
        exact hinc
      have h1' : loss (D i) u.val + 2 * ((Finset.univ : Finset (X × X)).filter
          (fun z => table (D i) z.1 z.2 = true ∧ targetI N t u.val z.1 z.2 = true)).card =
          A + N * t := h1
      have : 2 * (g + 1) * t = 2 * ((g + 1) * t) := by ring
      omega
    have hK_eval : ∀ (i : ℕ) (u : X),
        K i u = s * ((r * t) / N) +
          ((((u.val + q0) % N + (i + 1) * l) * s) / N -
           (((u.val + q0) % N + i * l) * s) / N) := by
      intro i u
      set a := (u.val + q0) % N
      have ha_lt : a < N := Nat.mod_lt _ hN
      have hK_sum : K i u = ∑ y ∈ Ci i, ∑ a' ∈ Finset.range r,
          (if targetI N t u.val (rowMap N t hN a') y = true then 1 else 0) := by
        simp only [K, Finset.card_filter, Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        have houter : ∀ y : Fin N,
            (∑ x : Fin N, if x ∈ R0 ∧ y ∈ Ci i ∧ targetI N t u.val x y = true then 1 else 0) =
            if y ∈ Ci i then ∑ a' ∈ Finset.range r,
              (if targetI N t u.val (rowMap N t hN a') y = true then 1 else 0) else 0 := by
          intro y
          by_cases hy : y ∈ Ci i
          · simp only [hy, true_and, ↓reduceIte]
            have hinner_x : ∀ x : Fin N,
                (if x ∈ R0 ∧ targetI N t u.val x y = true then 1 else 0) =
                if x ∈ R0 then (if targetI N t u.val x y = true then 1 else 0) else 0 := by
              intro x; by_cases hx : x ∈ R0 <;> simp [hx]
            rw [Finset.sum_congr rfl (fun x _ => hinner_x x),
              Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_image (rowMap_inj hN hr_lt)]
          · simp [hy]
        rw [Finset.sum_congr rfl (fun y _ => houter y), Finset.sum_ite_mem, Finset.univ_inter]
      rw [hK_sum]
      have hinner : ∀ y ∈ Ci i,
          ∑ a' ∈ Finset.range r, (if targetI N t u.val (rowMap N t hN a') y = true then 1 else 0) =
          (r * t) / N + (if ((shiftY i y).val + N - (a + i * l) % N) % N < l then 1 else 0) := by
        intro y _
        set zy : Fin N := ⟨(y.val + N - u.val) % N, Nat.mod_lt _ hN⟩
        have htg : ∀ a', targetI N t u.val (rowMap N t hN a') y =
            decide ((zy.val + N - (rowMap N t hN a').val) % N < t) := by
          intro a'
          simp only [targetI, Nat.mod_eq_of_lt u.isLt, zy]
          congr 1
          set x := (rowMap N t hN a').val
          have hx := (rowMap N t hN a').isLt
          have hy := y.isLt; have hu := u.isLt
          by_cases hyu : u.val ≤ y.val
          · have e1 : y.val + N - u.val = (y.val - u.val) + N := by omega
            rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : y.val - u.val < N)]
            have e2 : y.val + N - x + N - u.val = (y.val - u.val + N - x) + N := by omega
            rw [e2, Nat.add_mod_right]
          · rw [Nat.mod_eq_of_lt (by omega : y.val + N - u.val < N)]
            have e2 : y.val + N - x + N - u.val = (y.val + N - u.val) + N - x := by omega
            rw [e2]
        simp_rw [htg]
        have hir := inner_sum_rowMap hN ht hr_lt zy
        simp only [decide_eq_true_eq]
        rw [hir]
        congr 2

        have hLHS : (zy.val + N - q0) % N = (y.val + 2 * N - u.val - q0) % N := by
          have hy := y.isLt; have hu := u.isLt
          by_cases hyu : u.val ≤ y.val
          · have e1 : zy.val = y.val - u.val := by
              simp only [zy]
              have : y.val + N - u.val = (y.val - u.val) + N := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [e1]
            have : y.val + 2 * N - u.val - q0 = (y.val - u.val + N - q0) + N := by omega
            rw [this, Nat.add_mod_right]
          · have e1 : zy.val = y.val + N - u.val := by
              simp only [zy, Nat.mod_eq_of_lt (by omega : y.val + N - u.val < N)]
            rw [e1]
            have : y.val + N - u.val + N - q0 = y.val + 2 * N - u.val - q0 := by omega
            rw [this]
        have hRHS : ((shiftY i y).val + N - (a + i * l) % N) % N =
            (y.val + 2 * N - u.val - q0) % N := by
          have hy := y.isLt; have hu := u.isLt
          have hsh : (shiftY i y).val = (y.val + i * l) % N := by
            simp only [shiftY, l]
            rw [Nat.add_mod, Nat.add_mod y.val (i * (r * t % N))]
            congr 2
            rw [Nat.mul_assoc (i % N), Nat.mul_mod, Nat.mod_mod,
              Nat.mul_mod i, Nat.mod_mod]
          have hden : (a + i * l) % N = (u.val + q0 + i * l) % N := by
            simp only [a]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          rw [hsh, hden]
          set b := (i * l) % N
          have hb : b < N := Nat.mod_lt _ hN
          have hsh2 : (y.val + i * l) % N = (y.val + b) % N := by
            rw [Nat.add_mod, Nat.add_mod y.val, Nat.mod_mod]
          have hden2 : (u.val + q0 + i * l) % N = (u.val + q0 + b) % N := by
            rw [Nat.add_mod, Nat.add_mod (u.val + q0), Nat.mod_mod]
          rw [hsh2, hden2]
          set lhs := (y.val + b) % N
          set rhs := (u.val + q0 + b) % N
          have hlhs : lhs < N := Nat.mod_lt _ hN
          have hrhs : rhs < N := Nat.mod_lt _ hN
          have hadd_mod : (lhs + N - rhs + rhs) % N = (y.val + 2 * N - u.val - q0 + rhs) % N := by
            have e1 : lhs + N - rhs + rhs = lhs + N := by omega
            rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt hlhs]
            rw [Nat.add_mod, show rhs % N = (u.val + q0 + b) % N from Nat.mod_eq_of_lt hrhs,
              ← Nat.add_mod]
            have e2 : y.val + 2 * N - u.val - q0 + (u.val + q0 + b) = (y.val + b) + 2 * N := by omega
            rw [e2, Nat.add_mul_mod_self_right]
          have hcancel : ∀ v₁ v₂, v₁ < N → v₂ < N → (v₁ + rhs) % N = (v₂ + rhs) % N → v₁ = v₂ := by
            intro v₁ v₂ hv1 hv2 heq
            by_cases c1 : v₁ + rhs < N <;> by_cases c2 : v₂ + rhs < N
            · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at heq; omega
            · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega),
                Nat.mod_eq_of_lt (by omega)] at heq; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_of_lt c2] at heq; omega
            · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
                Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at heq; omega
          apply hcancel _ _ (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hadd_mod,
            Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        rw [hLHS, hRHS]
      rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_const, hCi_card i,
        smul_eq_mul]
      congr 1

      have hreidx : ∑ y ∈ Ci i, (if ((shiftY i y).val + N - (a + i * l) % N) % N < l then 1 else 0) =
          ∑ c ∈ C0, (if (c.val + N - (a + i * l) % N) % N < l then 1 else 0) := by
        refine Finset.sum_bij (fun y _ => shiftY i y) (fun y hy => by simpa [Ci] using hy)
          (fun a _ b _ h => (hshiftY_bij i).1 h) (fun c hc => ?_) (fun _ _ => rfl)
        obtain ⟨y, hy⟩ := (hshiftY_bij i).2 c
        exact ⟨y, by simpa [Ci, hy] using hc, hy⟩
      rw [hreidx]

      have hIco : ∑ c ∈ C0, (if (c.val + N - (a + i * l) % N) % N < l then 1 else 0) =
          ∑ k ∈ Finset.Ico (a + i * l) (a + (i + 1) * l), (((k + 1) * s) / N - (k * s) / N) := by
        have hl_lt : l < N := Nat.mod_lt _ hN
        have hstep1 : ∑ k ∈ Finset.Ico (a + i * l) (a + (i + 1) * l),
            (((k + 1) * s) / N - (k * s) / N) =
            ∑ k ∈ Finset.Ico (a + i * l) (a + (i + 1) * l),
              (if (⟨k % N, Nat.mod_lt _ hN⟩ : Fin N) ∈ C0 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [floor_diff_mod N s k hN, hC0_step (k % N)]
          simp [C0]
        rw [hstep1]
        rw [← Finset.sum_filter (p := fun k => (⟨k % N, Nat.mod_lt _ hN⟩ : Fin N) ∈ C0)]
        rw [← Finset.sum_filter (p := fun c : Fin N => (c.val + N - (a + i * l) % N) % N < l)]
        simp only [Finset.sum_const, smul_eq_mul, mul_one]
        symm
        refine Finset.card_bij (fun k _ => (⟨k % N, Nat.mod_lt _ hN⟩ : Fin N)) ?_ ?_ ?_
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
          refine ⟨hk.2, ?_⟩
          set d' := k - (a + i * l)
          have hd'_lt : d' < l := by rw [Nat.add_mul, one_mul] at hk; omega
          have hk_eq : k = (a + i * l) + d' := by omega
          have hmod_k : (k % N + N - (a + i * l) % N) % N = d' := by
            set r0 := (a + i * l) % N
            have hr0 : r0 < N := Nat.mod_lt _ hN
            have hk_mod : k % N = (r0 + d') % N := by
              rw [hk_eq]
              exact mod_add_left_eq _ _ _ _ (Nat.mod_eq_of_lt hr0).symm
            rw [hk_mod]
            by_cases hsum : r0 + d' < N
            · rw [Nat.mod_eq_of_lt hsum]
              have : r0 + d' + N - r0 = d' + N := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : d' < N)]
            · rw [Nat.mod_eq_sub_mod (by omega : N ≤ r0 + d'),
                Nat.mod_eq_of_lt (by omega : r0 + d' - N < N)]
              have : r0 + d' - N + N - r0 = d' := by omega
              rw [this, Nat.mod_eq_of_lt (by omega : d' < N)]
          rw [hmod_k]; exact hd'_lt
        · intro k₁ hk₁ k₂ hk₂ heq
          simp only [Finset.mem_filter, Finset.mem_Ico] at hk₁ hk₂
          have hv := congrArg Fin.val heq
          dsimp at hv
          set d₁ := k₁ - (a + i * l); set d₂ := k₂ - (a + i * l)
          have hd1 : d₁ < l := by rw [Nat.add_mul, one_mul] at hk₁; omega
          have hd2 : d₂ < l := by rw [Nat.add_mul, one_mul] at hk₂; omega
          have h1 : k₁ = a + i * l + d₁ := by omega
          have h2 : k₂ = a + i * l + d₂ := by omega
          have h3 : ((a + i * l) % N + d₁) % N = ((a + i * l) % N + d₂) % N := by
            have e1 : ((a + i * l) % N + d₁) % N = k₁ % N := by
              rw [h1]; exact mod_add_left_eq _ _ _ _ (Nat.mod_mod _ _)
            have e2 : ((a + i * l) % N + d₂) % N = k₂ % N := by
              rw [h2]; exact mod_add_left_eq _ _ _ _ (Nat.mod_mod _ _)
            rw [e1, e2, hv]
          set r0 := (a + i * l) % N
          have hr0 : r0 < N := Nat.mod_lt _ hN
          by_cases c1 : r0 + d₁ < N <;> by_cases c2 : r0 + d₂ < N
          · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at h3; omega
          · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega),
              Nat.mod_eq_of_lt (by omega)] at h3; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt c2] at h3; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega
        · intro c hc
          simp only [Finset.mem_filter] at hc
          set d' := (c.val + N - (a + i * l) % N) % N
          have hmod : (a + i * l + d') % N = c.val := by
            set r0 := (a + i * l) % N
            have hr0 : r0 < N := Nat.mod_lt _ hN
            have hstep : (a + i * l + d') % N = (r0 + d') % N :=
              mod_add_left_eq _ _ _ _ (Nat.mod_eq_of_lt hr0).symm
            rw [hstep]
            by_cases hrc : r0 ≤ c.val
            · have ed : d' = c.val - r0 := by
                simp only [d']
                have : c.val + N - r0 = (c.val - r0) + N := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [ed, Nat.add_sub_of_le hrc, Nat.mod_eq_of_lt c.isLt]
            · have ed : d' = c.val + N - r0 := by
                simp only [d']
                exact Nat.mod_eq_of_lt (by omega : c.val + N - r0 < N)
              rw [ed]
              have : r0 + (c.val + N - r0) = c.val + N := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt c.isLt]
          refine ⟨a + i * l + d', ?_, Fin.ext hmod⟩
          simp only [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, by rw [Nat.add_mul, one_mul]; omega⟩, ?_⟩
          convert hc.1 using 1
          exact Fin.ext hmod
      rw [hIco, sum_floor_diff_Ico N s (a + i * l) (a + (i + 1) * l)
        (by rw [Nat.add_mul, one_mul]; omega)]

    have hsumK : ∀ u : X, ∑ i : Fin M, K i.val u =
        M * (s * ((r * t) / N)) +
          ((((u.val + q0) % N + M * l) * s) / N - (((u.val + q0) % N) * s) / N) := by
      intro u
      set a := (u.val + q0) % N
      have h1 : ∑ i : Fin M, K i.val u =
          ∑ i ∈ Finset.range M, (s * ((r * t) / N) +
            (((a + (i + 1) * l) * s) / N - ((a + i * l) * s) / N)) := by
        rw [Fin.sum_univ_eq_sum_range (fun i => K i u)]
        exact Finset.sum_congr rfl (fun i _ => hK_eval i u)
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
      congr 1
      clear h1 hM
      induction M with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have hle1 : (a * s) / N ≤ ((a + m * l) * s) / N :=
          Nat.div_le_div_right (Nat.mul_le_mul_right s (by omega))
        have hle2 : ((a + m * l) * s) / N ≤ ((a + (m + 1) * l) * s) / N :=
          Nat.div_le_div_right (Nat.mul_le_mul_right s (by rw [Nat.add_mul, one_mul]; omega))
        omega

    have hN_total : ∀ u : X,
        N * total M (fun i => D i.val) u + 2 * (M * l * s) =
          M * bench + 2 * N *
            ((((u.val + q0) % N + M * l) * s) / N - (((u.val + q0) % N) * s) / N) := by
      intro u
      have hsum_loss : total M (fun i => D i.val) u + 2 * M * (g + 1) * t =
          M * (A + N * t) + 2 * ∑ i : Fin M, K i.val u := by
        have h1 : ∑ i : Fin M, (loss (D i.val) u.val + 2 * (g + 1) * t) =
            ∑ i : Fin M, (A + N * t + 2 * K i.val u) :=
          Finset.sum_congr rfl (fun i _ => hloss_K i.val u)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul, ← Finset.mul_sum] at h1
        change total M (fun i => D i.val) u + M * (2 * (g + 1) * t) =
          M * (A + N * t) + 2 * ∑ i : Fin M, K i.val u at h1
        linarith
      have hmulN := congrArg (N * ·) hsum_loss
      rw [hsumK u] at hmulN
      have hMpt : M * p * t = N * (M * (s * ((r * t) / N))) + M * l * s := by
        have hrt_div := Nat.div_add_mod (r * t) N
        calc M * p * t = M * s * (r * t) := by simp only [p]; ring
          _ = M * s * (N * ((r * t) / N) + l) := by rw [hrt_div]
          _ = N * (M * (s * ((r * t) / N))) + M * l * s := by ring
      have hbench_eq : bench + (2 * t - N) * A = N * (N * t) := Nat.sub_add_cancel h2tN_A
      have hAp : A + p = (g + 1) * N := Nat.sub_add_cancel hp_le_gN
      have h2tN_eq : (2 * t - N) * A + N * A = 2 * t * A := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
      have h2tAp : 2 * t * A + 2 * p * t = 2 * (g + 1) * t * N := by
        calc 2 * t * A + 2 * p * t = 2 * t * (A + p) := by ring
          _ = 2 * t * ((g + 1) * N) := by rw [hAp]
          _ = 2 * (g + 1) * t * N := by ring

      have hstep1 : N * total M (fun i => D i.val) u + 2 * N * M * (g + 1) * t =
          N * M * A + N * M * (N * t) + 2 * N * (M * (s * ((r * t) / N))) +
          2 * N * ((((u.val + q0) % N + M * l) * s) / N - (((u.val + q0) % N) * s) / N) := by
        zify at hmulN ⊢; linarith
      have hstep2 : M * bench + 2 * N * M * (g + 1) * t =
          N * M * A + N * M * (N * t) + 2 * (M * p * t) := by
        have hm1 : M * bench + M * ((2 * t - N) * A) = M * (N * (N * t)) := by
          rw [← Nat.mul_add, hbench_eq]
        have hm2 : M * ((2 * t - N) * A) + M * (N * A) = M * (2 * t * A) := by
          rw [← Nat.mul_add, h2tN_eq]
        have hm3 : M * (2 * t * A) + M * (2 * p * t) = M * (2 * (g + 1) * t * N) := by
          rw [← Nat.mul_add, h2tAp]
        zify at hm1 hm2 hm3 ⊢
        linarith
      zify at hstep1 hstep2 hMpt ⊢
      linarith

    have hrhs_eq : N * ((M * p * t + N - 1) / N) - M * p * t =
        N * ((M * l * s + N - 1) / N) - M * l * s := by
      have hMpt : M * p * t = N * (M * (s * ((r * t) / N))) + M * l * s := by
        have hrt_div := Nat.div_add_mod (r * t) N
        calc M * p * t = M * s * (r * t) := by simp only [p]; ring
          _ = M * s * (N * ((r * t) / N) + l) := by rw [hrt_div]
          _ = N * (M * (s * ((r * t) / N))) + M * l * s := by ring
      have hdiv : (M * p * t + N - 1) / N = M * (s * ((r * t) / N)) + (M * l * s + N - 1) / N := by
        have h1 : M * p * t + N - 1 = N * (M * (s * ((r * t) / N))) + (M * l * s + N - 1) := by omega
        rw [h1, Nat.mul_add_div hN]
      rw [hdiv, hMpt, Nat.mul_add]
      omega
    have hceil_ge : M * l * s ≤ N * ((M * l * s + N - 1) / N) := by
      have := Nat.div_add_mod (M * l * s + N - 1) N
      have := Nat.mod_lt (M * l * s + N - 1) hN
      omega
    have h2ceil : 2 * (N * ((M * l * s + N - 1) / N) - M * l * s) + 2 * (M * l * s) =
        2 * N * ((M * l * s + N - 1) / N) := by
      have hsub := Nat.mul_sub_left_distrib 2 (N * ((M * l * s + N - 1) / N)) (M * l * s)
      have h2m : 2 * (M * l * s) ≤ 2 * (N * ((M * l * s + N - 1) / N)) :=
        Nat.mul_le_mul_left 2 hceil_ge
      have hassoc : 2 * (N * ((M * l * s + N - 1) / N)) = 2 * N * ((M * l * s + N - 1) / N) := by
        ring
      omega

    apply le_antisymm
    · rw [Finset.sup_le_iff]
      intro u _
      have h1 := hN_total u
      have h2 := floor_diff_le_ceil N s ((u.val + q0) % N) (M * l) hN
      have h3 := Nat.mul_le_mul_left (2 * N) h2
      rw [hrhs_eq]
      omega
    ·
      have hsum_a := sum_floor_shift N s (M * l) hN
      have hex_a : ∃ a ∈ Finset.range N, (M * l * s + N - 1) / N ≤
          ((a + M * l) * s) / N - (a * s) / N := by
        by_contra hall
        push_neg at hall
        have hlt : ∑ a ∈ Finset.range N, (((a + M * l) * s) / N - (a * s) / N) <
            ∑ _a ∈ Finset.range N, ((M * l * s + N - 1) / N) := by
          apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
          exact hall
        rw [hsum_a, Finset.sum_const, Finset.card_range, smul_eq_mul] at hlt

        have hle_all : ∀ a ∈ Finset.range N,
            ((a + M * l) * s) / N - (a * s) / N ≤ (M * l * s + N - 1) / N - 1 := by
          intro a ha; have := hall a ha; omega
        have hsum_le := Finset.sum_le_sum hle_all
        rw [hsum_a, Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum_le
        have hceil_pos : 0 < (M * l * s + N - 1) / N := by
          by_contra hz; push_neg at hz; interval_cases ((M * l * s + N - 1) / N)
          have := hall 0 (Finset.mem_range.mpr hN)
          omega
        have : N * ((M * l * s + N - 1) / N - 1) < M * l * s := by
          have := Nat.div_add_mod (M * l * s + N - 1) N
          have := Nat.mod_lt (M * l * s + N - 1) hN
          have : N * ((M * l * s + N - 1) / N - 1) + N = N * ((M * l * s + N - 1) / N) := by
            rw [← Nat.mul_add_one, Nat.sub_add_cancel hceil_pos]
          omega
        omega
      rcases hex_a with ⟨a, ha, hge⟩
      simp only [Finset.mem_range] at ha
      let u : X := ⟨(a + N - q0) % N, Nat.mod_lt _ hN⟩
      have hu_eq : (u.val + q0) % N = a := by
        simp only [u]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have : a + N - q0 + q0 = a + N := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
      have h1 := hN_total u
      rw [hu_eq] at h1
      have h3 := Nat.mul_le_mul_left (2 * N) hge
      have hle_sup : N * total M (fun i => D i.val) u ≤
          Finset.univ.sup (fun u : X => N * total M (fun i => D i.val) u) :=
        Finset.le_sup (f := fun u : X => N * total M (fun i => D i.val) u) (Finset.mem_univ u)
      rw [hrhs_eq]
      omega

  refine ⟨⟨D, fun i => ⟨hD_fits i, hD_area i, hD_per i⟩, hD_shift, hD_sup⟩, ?_⟩
  intro M hM

  have havg : ∀ D' : Fin M → Circ, (∀ i, fits (D' i)) →
      M * bench ≤ ∑ u : X, total M D' u := by
    intro D' hD'
    have hswap : ∑ u : X, total M D' u = ∑ i : Fin M, ∑ u : X, loss (D' i) u.val := by
      simp only [total]; rw [Finset.sum_comm]
    rw [hswap]
    have hge_i : ∀ i : Fin M, bench ≤ ∑ u : X, loss (D' i) u.val := by
      intro i
      have harea_le := area_le_A hg hN_gt hrs hd0 hdrs hrsN hmin (D' i)
        (hD' i).1 (hD' i).2.1 (hD' i).2.2
      have hsum_i := sum_loss_eq hNt ht (fun z => table (D' i) z.1 z.2)
      have hmul_le : (2 * t - N) * area (D' i) ≤ (2 * t - N) * A :=
        Nat.mul_le_mul_left _ harea_le
      have hbench_eq : bench + (2 * t - N) * A = N * (N * t) := Nat.sub_add_cancel h2tN_A
      change ∑ u : X, loss (D' i) u.val + (2 * t - N) * area (D' i) = N * (N * t) at hsum_i
      omega
    calc M * bench = ∑ _i : Fin M, bench := by simp
      _ ≤ ∑ i : Fin M, ∑ u : X, loss (D' i) u.val := Finset.sum_le_sum (fun i _ => hge_i i)
  refine ⟨?_, ?_⟩
  · intro D' hD'
    have h1 := havg D' hD'
    by_contra hall
    push_neg at hall
    have hlt : ∑ u : X, N * total M D' u < ∑ _u : X, (M * bench) := by
      apply Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
      exact fun u _ => hall u
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    have := Nat.mul_le_mul_left N h1
    omega
  ·
    constructor
    · rintro ⟨D', hD', hle_all⟩
      have h1 := havg D' hD'
      have hsum_le : ∑ u : X, N * total M D' u ≤ ∑ _u : X, (M * bench) :=
        Finset.sum_le_sum (fun u _ => hle_all u)
      rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_le
      have hsum_eq : ∑ u : X, total M D' u = M * bench := by
        have := Nat.le_of_mul_le_mul_left hsum_le hN
        omega

      have harea_eq : ∀ i : Fin M, area (D' i) = A := by
        have hswap : ∑ u : X, total M D' u = ∑ i : Fin M, ∑ u : X, loss (D' i) u.val := by
          simp only [total]; rw [Finset.sum_comm]
        rw [hswap] at hsum_eq
        have hge_i : ∀ i : Fin M, bench ≤ ∑ u : X, loss (D' i) u.val := by
          intro i
          have harea_le := area_le_A hg hN_gt hrs hd0 hdrs hrsN hmin (D' i)
            (hD' i).1 (hD' i).2.1 (hD' i).2.2
          have hsum_i := sum_loss_eq hNt ht (fun z => table (D' i) z.1 z.2)
          have hmul_le : (2 * t - N) * area (D' i) ≤ (2 * t - N) * A :=
            Nat.mul_le_mul_left _ harea_le
          have hbench_eq : bench + (2 * t - N) * A = N * (N * t) := Nat.sub_add_cancel h2tN_A
          change ∑ u : X, loss (D' i) u.val + (2 * t - N) * area (D' i) = N * (N * t) at hsum_i
          omega
        intro i
        have hi_eq : ∑ u : X, loss (D' i) u.val = bench := by
          by_contra hne
          have hlt_i : bench < ∑ u : X, loss (D' i) u.val := lt_of_le_of_ne (hge_i i) (Ne.symm hne)
          have hlt_sum : ∑ _j : Fin M, bench < ∑ j : Fin M, ∑ u : X, loss (D' j) u.val := by
            exact Finset.sum_lt_sum (fun j _ => hge_i j) ⟨i, Finset.mem_univ i, hlt_i⟩
          simp at hlt_sum; omega
        have hsum_i := sum_loss_eq hNt ht (fun z => table (D' i) z.1 z.2)
        have hbench_eq : bench + (2 * t - N) * A = N * (N * t) := Nat.sub_add_cancel h2tN_A
        change ∑ u : X, loss (D' i) u.val + (2 * t - N) * area (D' i) = N * (N * t) at hsum_i
        rw [hi_eq] at hsum_i
        have : (2 * t - N) * area (D' i) = (2 * t - N) * A := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * t - N) this

      let u0 : X := ⟨0, hN⟩
      have hu0_eq : N * total M D' u0 = M * bench := by
        by_contra hne
        have hlt_0 : N * total M D' u0 < M * bench := lt_of_le_of_ne (hle_all u0) hne
        have hlt_sum : ∑ u : X, N * total M D' u < ∑ _u : X, (M * bench) :=
          Finset.sum_lt_sum (fun u _ => hle_all u) ⟨u0, Finset.mem_univ u0, hlt_0⟩
        rw [← Finset.mul_sum, hsum_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul] at hlt_sum
        omega

      set S := ∑ i : Fin M, ((Finset.univ : Finset (X × X)).filter
        (fun z => table (D' i) z.1 z.2 = true ∧ targetI N t 0 z.1 z.2 = true)).card
      have htot0 : total M D' u0 + 2 * S = M * A + M * (N * t) := by
        have h1 : ∑ i : Fin M, (loss (D' i) 0 + 2 * ((Finset.univ : Finset (X × X)).filter
            (fun z => table (D' i) z.1 z.2 = true ∧ targetI N t 0 z.1 z.2 = true)).card) =
            ∑ i : Fin M, (A + N * t) := by
          apply Finset.sum_congr rfl
          intro i _
          have := loss_add_two_overlap ht (fun z => table (D' i) z.1 z.2) 0
          change loss (D' i) 0 + _ = area (D' i) + N * t at this
          rw [harea_eq i] at this
          exact this
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul] at h1
        change total M D' u0 + 2 * S = M * (A + N * t) at h1
        linarith
      have hbench_eq : bench + (2 * t - N) * A = N * (N * t) := Nat.sub_add_cancel h2tN_A
      have h2tN_eq : (2 * t - N) * A + N * A = 2 * t * A := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
      have hNS : N * S = M * t * A := by
        have hmul := congrArg (N * ·) htot0
        have h1 : M * bench + 2 * N * S = N * M * A + N * M * (N * t) := by
          zify at hmul hu0_eq ⊢; linarith
        have h2 : M * bench + M * ((2 * t - N) * A) = M * (N * (N * t)) := by
          rw [← Nat.mul_add, hbench_eq]
        have h3 : M * ((2 * t - N) * A) + M * (N * A) = M * (2 * t * A) := by
          rw [← Nat.mul_add, h2tN_eq]
        zify at h1 h2 h3 ⊢
        linarith
      have hAp : A + p = (g + 1) * N := Nat.sub_add_cancel hp_le_gN
      have hMpt_eq : N * S + M * p * t = N * (M * t * (g + 1)) := by
        calc N * S + M * p * t = M * t * A + M * t * p := by rw [hNS]; ring
          _ = M * t * (A + p) := by ring
          _ = M * t * ((g + 1) * N) := by rw [hAp]
          _ = N * (M * t * (g + 1)) := by ring
      refine ⟨M * t * (g + 1) - S, ?_⟩
      have hS_le : S ≤ M * t * (g + 1) := by
        have : N * S ≤ N * (M * t * (g + 1)) := by omega
        exact Nat.le_of_mul_le_mul_left this hN
      have : N * (M * t * (g + 1) - S) + N * S = N * (M * t * (g + 1)) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hS_le]
      omega
    · intro hdvd
      refine ⟨fun i => D i.val, fun i => hD_fits i.val, ?_⟩
      have hsup := hD_sup M hM
      rcases hdvd with ⟨k, hk⟩
      have hdiv : (M * p * t + N - 1) / N = k := by
        cases k with
        | zero =>
          simp only [mul_zero] at hk
          rw [hk, zero_add]
          exact Nat.div_eq_of_lt (by omega)
        | succ k' =>
          have h1 : M * p * t + N - 1 = N * (k' + 1) + (N - 1) := by omega
          rw [h1, Nat.mul_add_div hN, Nat.div_eq_of_lt (by omega : N - 1 < N), add_zero]
      rw [hdiv, ← hk, Nat.sub_self, mul_zero, add_zero] at hsup
      intro u
      calc N * total M (fun i => D i.val) u
          ≤ Finset.univ.sup (fun u : X => N * total M (fun i => D i.val) u) :=
            Finset.le_sup (f := fun u : X => N * total M (fun i => D i.val) u) (Finset.mem_univ u)
        _ = M * bench := hsup
