import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_566_aux

def up (d : ℕ) (A B : Finset ℕ) : Prop :=
  B.card ≤ d ∧ ∃ i : ℕ, 0 < i ∧ i ∉ A ∧ B = insert i A ∧ (i = 1 ∨ i - 1 ∈ A)

def step (d : ℕ) (U V : Finset ℕ) : Prop :=
  up d U V ∨ up d V U

def reachFrom (d : ℕ) (A B : Finset ℕ) : Prop :=
  Relation.ReflTransGen (step d) A B

def extElem (d j : ℕ) : ℕ :=
  2 ^ d - 2 ^ (d - (j + 1))

def extremal (d t : ℕ) : Finset ℕ :=
  (Finset.range t).image (extElem d)

def leftPred (S : Finset ℕ) (x : ℕ) : ℕ :=
  (S.filter (· < x)).sup id

def gap (S : Finset ℕ) (x : ℕ) : ℕ :=
  x - leftPred S x

inductive Clearable (d : ℕ) : Finset ℕ → Prop
  | empty : Clearable d ∅
  | step {S : Finset ℕ} {x : ℕ}
      (hx : x ∈ S)
      (hcard : S.card ≤ d)
      (hgap : gap S x ≤ 2 ^ (d - S.card))
      (hrest : Clearable d (S.erase x)) :
      Clearable d S

lemma step_symm {d : ℕ} {U V : Finset ℕ} (h : step d U V) : step d V U := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

lemma reachFrom_symm {d : ℕ} {A B : Finset ℕ} (h : reachFrom d A B) : reachFrom d B A := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact Relation.ReflTransGen.head (step_symm hab) ih

lemma pow_two_lt_of_lt {a b : ℕ} (h : a < b) : 2 ^ a < 2 ^ b :=
  Nat.pow_lt_pow_right (by decide : 1 < 2) h

lemma pow_two_le_of_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

lemma extElem_strictMono {d j1 j2 : ℕ} (h12 : j1 < j2) (h2 : j2 < d) :
    extElem d j1 < extElem d j2 := by
  unfold extElem
  have hlt : d - (j2 + 1) < d - (j1 + 1) := by omega
  have hle : d - (j1 + 1) ≤ d := by omega
  have hp1 : 2 ^ (d - (j2 + 1)) < 2 ^ (d - (j1 + 1)) := pow_two_lt_of_lt hlt
  have hp2 : 2 ^ (d - (j1 + 1)) ≤ 2 ^ d := pow_two_le_of_le hle
  omega

lemma extremal_zero (d : ℕ) : extremal d 0 = ∅ := by
  simp [extremal]

lemma extremal_succ (d t : ℕ) :
    extremal d (t + 1) = insert (extElem d t) (extremal d t) := by
  unfold extremal
  rw [Finset.range_add_one, Finset.image_insert]

lemma extremal_card {d t : ℕ} (ht : t ≤ d) : (extremal d t).card = t := by
  unfold extremal
  rw [Finset.card_image_of_injOn]
  · exact Finset.card_range t
  · intro j1 hj1 j2 hj2 heq
    rw [Finset.mem_coe, Finset.mem_range] at hj1 hj2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd heq (ne_of_lt (extElem_strictMono hlt (by omega)))
    · exact absurd heq.symm (ne_of_lt (extElem_strictMono hgt (by omega)))

lemma extremal_sup {d t : ℕ} (ht : t ≤ d) : (extremal d t).sup id = 2 ^ d - 2 ^ (d - t) := by
  cases t with
  | zero =>
    simp [extremal]
  | succ k =>
    apply le_antisymm
    · apply Finset.sup_le
      intro y hy
      unfold extremal at hy
      rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      rw [Finset.mem_range] at hj
      unfold extElem
      simp only [id_eq]
      have hle : d - (k + 1) ≤ d - (j + 1) := by omega
      have hp : 2 ^ (d - (k + 1)) ≤ 2 ^ (d - (j + 1)) := pow_two_le_of_le hle
      omega
    · have hmem : 2 ^ d - 2 ^ (d - (k + 1)) ∈ extremal d (k + 1) := by
        unfold extremal
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
      exact Finset.le_sup (f := id) hmem

lemma extremal_le_limit {d t : ℕ} (ht : t ≤ d) {x : ℕ} (hx : x ∈ extremal d t) :
    x ≤ 2 ^ d - 2 ^ (d - t) := by
  calc x ≤ (extremal d t).sup id := Finset.le_sup (f := id) hx
    _ = 2 ^ d - 2 ^ (d - t) := extremal_sup ht

lemma bridge (d : ℕ) : ∀ (k : ℕ) (F : Finset ℕ) (a : ℕ),
    F.card + (k + 1) ≤ d →
    (a = 0 ∨ a ∈ F) →
    (∀ x ∈ F, x ≤ a ∨ a + 2 ^ k < x) →
    reachFrom d F (insert (a + 2 ^ k) F)
  | 0, F, a, hcard, ha, hdisj => by
    apply Relation.ReflTransGen.single
    apply Or.inl
    have hnotmem : a + 1 ∉ F := by
      intro hmem
      have h := hdisj (a + 1) hmem
      simp at h
    refine ⟨?_, a + 1, by omega, hnotmem, by simp, ?_⟩
    · simp only [Nat.pow_zero]
      rw [Finset.card_insert_of_notMem hnotmem]
      omega
    · rcases ha with rfl | hmem
      · exact Or.inl rfl
      · exact Or.inr (by simpa using hmem)
  | k + 1, F, a, hcard, ha, hdisj => by
    set m := a + 2 ^ k with hm_def
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    have hp2 : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ]
      omega
    have hpow : a + 2 ^ (k + 1) = m + 2 ^ k := by
      rw [hm_def, hp2]
      omega
    have hm_notmem : m ∉ F := by
      intro hmem
      have h := hdisj m hmem
      omega
    have htop_notmem : m + 2 ^ k ∉ F := by
      intro hmem
      have h := hdisj (m + 2 ^ k) hmem
      omega
    have h1 : reachFrom d F (insert m F) :=
      bridge d k F a (by omega) ha (fun x hx => by
        rcases hdisj x hx with hle | hgt
        · exact Or.inl hle
        · exact Or.inr (by omega))
    have h2 : reachFrom d (insert m F) (insert (m + 2 ^ k) (insert m F)) :=
      bridge d k (insert m F) m
        (by rw [Finset.card_insert_of_notMem hm_notmem]; omega)
        (Or.inr (Finset.mem_insert_self m F))
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxF
          · exact Or.inl (le_refl m)
          · rcases hdisj x hxF with hle | hgt
            · exact Or.inl (by omega)
            · exact Or.inr (by omega))
    have h3 : reachFrom d (insert (m + 2 ^ k) F) (insert m (insert (m + 2 ^ k) F)) :=
      bridge d k (insert (m + 2 ^ k) F) a
        (by rw [Finset.card_insert_of_notMem htop_notmem]; omega)
        (by rcases ha with rfl | hmem
            · exact Or.inl rfl
            · exact Or.inr (Finset.mem_insert_of_mem hmem))
        (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hxF
          · have hp : 0 < 2 ^ k := Nat.two_pow_pos k
            exact Or.inr (by omega)
          · rcases hdisj x hxF with hle | hgt
            · exact Or.inl hle
            · exact Or.inr (by omega))
    have h3' : reachFrom d (insert (m + 2 ^ k) (insert m F)) (insert (m + 2 ^ k) F) := by
      rw [Finset.insert_comm]
      exact reachFrom_symm h3
    rw [hpow]
    exact h1.trans (h2.trans h3')

lemma reach_extremal (d : ℕ) : ∀ t : ℕ, t ≤ d → reachFrom d ∅ (extremal d t)
  | 0, _ => by
    rw [extremal_zero]
    exact .refl
  | t + 1, ht => by
    have ih : reachFrom d ∅ (extremal d t) := reach_extremal d t (by omega)
    rw [extremal_succ]
    cases t with
    | zero =>
      rw [extremal_zero]
      have hcard : (∅ : Finset ℕ).card + ((d - 1) + 1) ≤ d := by simp; omega
      have hbr := bridge d (d - 1) ∅ 0 hcard (Or.inl rfl) (by simp)
      have heq : 0 + 2 ^ (d - 1) = extElem d 0 := by
        unfold extElem
        simp only [Nat.zero_add]
        have hd : 1 ≤ d := by omega
        have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hd]
          rw [Nat.pow_succ]
          omega
        omega
      rwa [heq] at hbr
    | succ k =>
      set F := extremal d (k + 1) with hF_def
      set a := extElem d k with ha_def
      have ha_mem : a ∈ F := by
        rw [hF_def, extremal_succ]
        exact Finset.mem_insert_self _ _
      have hcard : F.card + ((d - (k + 2)) + 1) ≤ d := by
        rw [hF_def, extremal_card (by omega)]
        omega
      have hdisj : ∀ x ∈ F, x ≤ a ∨ a + 2 ^ (d - (k + 2)) < x := by
        intro x hx
        left
        have hle := extremal_le_limit (by omega : k + 1 ≤ d) hx
        exact hle
      have hbr := bridge d (d - (k + 2)) F a hcard (Or.inr ha_mem) hdisj
      have heq : a + 2 ^ (d - (k + 2)) = extElem d (k + 1) := by
        rw [ha_def]
        unfold extElem
        have hk : k + 1 + 1 = k + 2 := rfl
        rw [hk]
        have h1 : d - (k + 1) = (d - (k + 2)) + 1 := by omega
        have h2 : 2 ^ (d - (k + 1)) = 2 * 2 ^ (d - (k + 2)) := by
          rw [h1, Nat.pow_succ]
          omega
        have h3 : 2 ^ (d - (k + 1)) ≤ 2 ^ d := pow_two_le_of_le (by omega)
        omega
      rw [heq] at hbr
      exact ih.trans hbr

lemma finset_sup_mem (s : Finset ℕ) (hs : s.Nonempty) : s.sup id ∈ s := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | @insert a t ha ih =>
    by_cases ht : t.Nonempty
    · rw [Finset.sup_insert]
      simp only [id_eq]
      by_cases h : a ≤ t.sup id
      · rw [sup_eq_right.mpr h]
        exact Finset.mem_insert_of_mem (ih ht)
      · rw [sup_eq_left.mpr (le_of_not_ge h)]
        exact Finset.mem_insert_self a t
    · rw [Finset.not_nonempty_iff_eq_empty.mp ht]
      simp

lemma leftPred_le (S : Finset ℕ) (x : ℕ) : leftPred S x ≤ x := by
  unfold leftPred
  apply Finset.sup_le
  intro y hy
  rw [Finset.mem_filter] at hy
  exact le_of_lt hy.2

lemma gap_erase_le {S : Finset ℕ} {x y k : ℕ}
    (_hxy : x ≠ y)
    (hx : gap S x ≤ 2 ^ k)
    (hy : gap S y ≤ 2 ^ k) :
    gap (S.erase x) y ≤ 2 ^ (k + 1) := by
  by_cases hxeq : x = leftPred S y
  · have hsub : S.filter (· < x) ⊆ (S.erase x).filter (· < y) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      have hxy_le : x ≤ y := by
        rw [hxeq]
        exact leftPred_le S y
      refine ⟨Finset.mem_erase.mpr ⟨ne_of_lt hz.2, hz.1⟩, lt_of_lt_of_le hz.2 hxy_le⟩
    have hpred : leftPred S x ≤ leftPred (S.erase x) y :=
      Finset.sup_mono hsub
    have hx_le_y : x ≤ y := by
      rw [hxeq]
      exact leftPred_le S y
    have hpx_le_x : leftPred S x ≤ x := leftPred_le S x
    unfold gap at hx hy ⊢
    rw [← hxeq] at hy
    rw [Nat.pow_succ]
    omega
  · have heq : leftPred (S.erase x) y = leftPred S y := by
      apply le_antisymm
      · apply Finset.sup_mono
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨Finset.mem_of_mem_erase hz.1, hz.2⟩
      · by_cases hne : (S.filter (· < y)).Nonempty
        · have hm : leftPred S y ∈ S.filter (· < y) := finset_sup_mem _ hne
          rw [Finset.mem_filter] at hm
          have hm' : leftPred S y ∈ (S.erase x).filter (· < y) :=
            Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨Ne.symm hxeq, hm.1⟩, hm.2⟩
          exact Finset.le_sup (f := id) hm'
        · unfold leftPred
          rw [Finset.not_nonempty_iff_eq_empty.mp hne]
          simp
    unfold gap at hy ⊢
    rw [heq, Nat.pow_succ]
    omega

lemma clearable_erase {d : ℕ} {S : Finset ℕ} (hS : Clearable d S) :
    ∀ {y : ℕ}, y ∈ S → gap S y ≤ 2 ^ (d - S.card) → Clearable d (S.erase y) := by
  induction hS with
  | empty =>
    intro y hy
    simp at hy
  | @step S x hx hcard hgap hrest ih =>
    intro y hy hgap_y
    by_cases hxy : x = y
    · subst hxy
      exact hrest
    · have hy' : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
      have hx' : x ∈ S.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
      have hcard_x : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
      have hcard_y : (S.erase y).card = S.card - 1 := Finset.card_erase_of_mem hy
      have hd_x : d - (S.erase x).card = (d - S.card) + 1 := by omega
      have hd_y : d - (S.erase y).card = (d - S.card) + 1 := by omega
      have hgy' : gap (S.erase x) y ≤ 2 ^ (d - (S.erase x).card) := by
        rw [hd_x]
        exact gap_erase_le hxy hgap hgap_y
      have hgx' : gap (S.erase y) x ≤ 2 ^ (d - (S.erase y).card) := by
        rw [hd_y]
        exact gap_erase_le (Ne.symm hxy) hgap_y hgap
      have hxy_clear : Clearable d ((S.erase x).erase y) := ih hy' hgy'
      rw [Finset.erase_right_comm] at hxy_clear
      exact Clearable.step hx' (by omega) hgx' hxy_clear

lemma gap_insert_up {U : Finset ℕ} {i : ℕ} (hi_pos : 0 < i) (hi_adj : i = 1 ∨ i - 1 ∈ U) :
    gap (insert i U) i ≤ 1 := by
  unfold gap
  rcases hi_adj with rfl | hmem
  · omega
  · have hmem' : i - 1 ∈ (insert i U).filter (· < i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hmem, by omega⟩
    have hle : i - 1 ≤ leftPred (insert i U) i := Finset.le_sup (f := id) hmem'
    omega

lemma reach_clearable {d : ℕ} {S : Finset ℕ} (h : reachFrom d ∅ S) : Clearable d S := by
  induction h with
  | refl => exact Clearable.empty
  | @tail U V _ hstep ih =>
    rcases hstep with hup | hdown
    · rcases hup with ⟨hVcard, i, hi_pos, hi_notmem, rfl, hi_adj⟩
      have hgap : gap (insert i U) i ≤ 2 ^ (d - (insert i U).card) := by
        have h1 := gap_insert_up hi_pos hi_adj
        have h2 : 1 ≤ 2 ^ (d - (insert i U).card) := Nat.one_le_two_pow
        omega
      have herase : (insert i U).erase i = U := Finset.erase_insert hi_notmem
      exact Clearable.step (Finset.mem_insert_self i U) hVcard hgap (by rwa [herase])
    · rcases hdown with ⟨_, i, hi_pos, hi_notmem, hUeq, hi_adj⟩
      have hgap : gap U i ≤ 2 ^ (d - U.card) := by
        rw [hUeq]
        have h1 := gap_insert_up hi_pos hi_adj
        have h2 : 1 ≤ 2 ^ (d - (insert i V).card) := Nat.one_le_two_pow
        omega
      have hi_mem : i ∈ U := by
        rw [hUeq]
        exact Finset.mem_insert_self i V
      have hclear := clearable_erase ih hi_mem hgap
      have herase : U.erase i = V := by
        rw [hUeq]
        exact Finset.erase_insert hi_notmem
      rwa [herase] at hclear

lemma clearable_bound {d : ℕ} {S : Finset ℕ} (hS : Clearable d S) :
    S.sup id ≤ 2 ^ d - 2 ^ (d - S.card) ∧
      (S.sup id = 2 ^ d - 2 ^ (d - S.card) → S = extremal d S.card) := by
  induction hS with
  | empty =>
    simp [extremal_zero]
  | @step S x hx hcard hgap hrest ih =>
    rcases ih with ⟨ih_le, ih_eq⟩
    set S' := S.erase x with hS'_def
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
    have hcard' : S'.card = S.card - 1 := Finset.card_erase_of_mem hx
    have hS_ins : insert x S' = S := Finset.insert_erase hx
    have hsup_eq : S.sup id = x ⊔ S'.sup id := by
      conv_lhs => rw [← hS_ins]
      rw [Finset.sup_insert]
      rfl
    have hpow_step : 2 ^ (d - (S.card - 1)) = 2 * 2 ^ (d - S.card) := by
      have h1 : d - (S.card - 1) = (d - S.card) + 1 := by omega
      rw [h1, Nat.pow_succ]
      omega
    have hpow_le_d : 2 ^ (d - (S.card - 1)) ≤ 2 ^ d := pow_two_le_of_le (by omega)
    have hpow_pos : 0 < 2 ^ (d - S.card) := Nat.two_pow_pos _
    rw [hcard'] at ih_le ih_eq
    by_cases hxle : x ≤ S'.sup id
    · have hsup : S.sup id = S'.sup id := by
        rw [hsup_eq, sup_eq_right.mpr hxle]
      have hstrict : S.sup id < 2 ^ d - 2 ^ (d - S.card) := by
        rw [hsup]
        omega
      exact ⟨le_of_lt hstrict, fun heq => absurd heq (ne_of_lt hstrict)⟩
    · have hxgt : S'.sup id < x := lt_of_not_ge hxle
      have hsup : S.sup id = x := by
        rw [hsup_eq, sup_eq_left.mpr (le_of_lt hxgt)]
      have hfilt : S.filter (· < x) = S' := by
        ext y
        rw [Finset.mem_filter, hS'_def, Finset.mem_erase]
        constructor
        · intro ⟨hyS, hylt⟩
          exact ⟨ne_of_lt hylt, hyS⟩
        · intro ⟨hyne, hyS⟩
          refine ⟨hyS, lt_of_le_of_lt ?_ hxgt⟩
          exact Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨hyne, hyS⟩)
      have hlp : leftPred S x = S'.sup id := by
        unfold leftPred
        rw [hfilt]
      have hgap_eq : gap S x = x - S'.sup id := by
        unfold gap
        rw [hlp]
      have hbound : S.sup id ≤ 2 ^ d - 2 ^ (d - S.card) := by
        rw [hsup]
        omega
      refine ⟨hbound, fun heq => ?_⟩
      have hS'_sup_eq : S'.sup id = 2 ^ d - 2 ^ (d - (S.card - 1)) := by
        rw [hsup] at heq
        omega
      have hS'_ext : S' = extremal d (S.card - 1) := ih_eq hS'_sup_eq
      have hx_ext : x = extElem d (S.card - 1) := by
        rw [hsup] at heq
        unfold extElem
        have h1 : S.card - 1 + 1 = S.card := by omega
        rw [h1]
        exact heq
      conv_lhs => rw [← hS_ins, hS'_ext, hx_ext]
      have h2 : S.card = (S.card - 1) + 1 := by omega
      conv_rhs => rw [h2, extremal_succ]

end PEqualNP.Outside.L_lib_566_aux

theorem PEqualNP.Outside.L_lib_566 :
∀ (d t : ℕ), t ≤ d →
  let up := fun A B : Finset ℕ => B.card ≤ d ∧
    ∃ i : ℕ, 0 < i ∧ i ∉ A ∧ B = insert i A ∧ (i = 1 ∨ i-1 ∈ A)
  let reach := fun S : Finset ℕ =>
    Relation.ReflTransGen (fun U V => up U V ∨ up V U) ∅ S
  let limit := 2^d - 2^(d-t)
  let extremal := (Finset.range t).image (fun j => 2^d - 2^(d-(j+1)))
  reach extremal ∧ extremal.card = t ∧ extremal.sup id = limit ∧
    ∀ S : Finset ℕ, reach S → S.card = t →
      S.sup id ≤ limit ∧ (S.sup id = limit ↔ S = extremal) := by
  intro d t ht
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_lib_566_aux.reach_extremal d t ht
  · exact PEqualNP.Outside.L_lib_566_aux.extremal_card ht
  · exact PEqualNP.Outside.L_lib_566_aux.extremal_sup ht
  · intro S hreach hcard
    have hcl := PEqualNP.Outside.L_lib_566_aux.reach_clearable hreach
    have hb := PEqualNP.Outside.L_lib_566_aux.clearable_bound hcl
    rw [hcard] at hb
    refine ⟨hb.1, ⟨hb.2, ?_⟩⟩
    intro hSeq
    rw [hSeq]
    exact PEqualNP.Outside.L_lib_566_aux.extremal_sup ht
