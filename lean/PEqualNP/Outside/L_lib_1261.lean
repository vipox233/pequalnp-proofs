import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_1261 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n : Nat) (rk : Finset (Fin n) → Nat),
  rk ∅=0 → Monotone rk → (∀ x, rk x ≤ x.card) →
  (∀ x y, rk (x∪y)+rk (x∩y) ≤ rk x+rk y) →
  let f := fun (x : Finset (Fin n)) (j : Fin n) => decide (rk x < rk (insert j x))
  let named := fun (js : List (Fin n)) (x : Finset (Fin n)) =>
    List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u j=true ∧ f v j=false) js x
  (∀ x y, x ⊆ y → ∀ j, f y j=true → f x j=true) ∧
  (∀ x k, (∃ js : List (Fin n), js.length=k ∧ named js x) ↔ k ≤ rk x) ∧
  (∀ x js, (∀ j ∈ js, j ∈ x) → (named js x ↔ js.Nodup ∧ rk js.toFinset = js.length)) ∧
  ∀ H : Fin n → Fin n → Prop,
    let neigh := fun j => (Finset.univ : Finset (Fin n)).filter (fun i => H i j)
    ((∀ x j, (∀ i ∈ x, H i j) → f x j=true) ∧ (∀ x j, j ∈ x → f x j=false)) ↔
      ∀ j, rk (neigh j) < rk (insert j (neigh j))) := by
  let _inst : ∀ P : Prop, Decidable P := Classical.propDecidable
  letI := _inst
  intro n rk h0 hmono hcard hsub
  dsimp only
  set f : Finset (Fin n) → Fin n → Bool := fun x j => decide (rk x < rk (insert j x))
  set named : List (Fin n) → Finset (Fin n) → Prop := fun js x =>
    List.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
      (fun j _ prev y => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false) js x
  have hf_true : ∀ x j, f x j = true ↔ rk x < rk (insert j x) := by
    intro x j; simp [f]
  have hf_false : ∀ x j, f x j = false ↔ rk (insert j x) ≤ rk x := by
    intro x j; simp [f]
  have hrk_ins_le : ∀ x j, rk (insert j x) ≤ rk x + 1 := by
    intro x j
    have h1 := hsub x {j}
    have h2 : rk {j} ≤ 1 := by simpa using hcard {j}
    have h3 : x ∪ {j} = insert j x := by ext a; simp
    rw [h3] at h1
    linarith
  have hrk_ins_eq : ∀ x j, f x j = false → rk (insert j x) = rk x := by
    intro x j hf
    exact Nat.le_antisymm ((hf_false x j).mp hf) (hmono (Finset.subset_insert j x))
  have hrk_ins_succ : ∀ x j, f x j = true → rk (insert j x) = rk x + 1 := by
    intro x j ht
    exact Nat.le_antisymm (hrk_ins_le x j) ((hf_true x j).mp ht)
  have h_anti : ∀ x y, x ⊆ y → ∀ j, f y j = true → f x j = true := by
    intro x y hxy j hy
    rw [hf_true] at hy ⊢
    have h1 := hsub (insert j x) y
    have hu : insert j x ∪ y = insert j y := by
      ext a; simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ((rfl | ha) | ha)
        · exact Or.inl rfl
        · exact Or.inr (hxy ha)
        · exact Or.inr ha
      · rintro (rfl | ha)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ha
    have hi : x ⊆ insert j x ∩ y := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem ha, hxy ha⟩
    have hmi : rk x ≤ rk (insert j x ∩ y) := hmono hi
    rw [hu] at h1
    linarith
  have h_anti_false : ∀ x y, x ⊆ y → ∀ j, f x j = false → f y j = false := by
    intro x y hxy j hx
    cases hy : f y j
    · rfl
    · have := h_anti x y hxy j hy
      rw [hx] at this
      cases this
  have hrk_union_closed : ∀ s u, (∀ j ∈ s, f u j = false) → rk (s ∪ u) = rk u := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro u _; simp
    | @insert a s ha ih =>
      intro u hcl
      have hsu : rk (s ∪ u) = rk u := ih u (fun j hj => hcl j (Finset.mem_insert_of_mem hj))
      have ha_cl : f (s ∪ u) a = false :=
        h_anti_false u (s ∪ u) Finset.subset_union_right a (hcl a (Finset.mem_insert_self a s))
      have h1 : rk (insert a (s ∪ u)) = rk (s ∪ u) := hrk_ins_eq (s ∪ u) a ha_cl
      rw [Finset.insert_union, h1, hsu]
  have h_named_inv : ∀ js y, named js y →
      (∀ j ∈ js, f y j = false) ∧ js.Nodup ∧ rk js.toFinset = js.length ∧ js.length ≤ rk y := by
    intro js
    induction js with
    | nil =>
      intro y _
      refine ⟨by simp, List.nodup_nil, by simp [h0], Nat.zero_le _⟩
    | cons j js ih =>
      intro y hny
      rcases hny with ⟨u, v, hnu, huv, hvy, huj, hvj⟩
      rcases ih u hnu with ⟨hu_cl, hnd, hrk_js, _⟩
      have huy : u ⊆ y := huv.trans hvy
      have hy_cl : ∀ i ∈ j :: js, f y i = false := by
        intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact h_anti_false v y hvy i hvj
        · exact h_anti_false u y huy i (hu_cl i hi)
      have hj_not_mem : j ∉ js := by
        intro hj
        have h1 := hu_cl j hj
        rw [huj] at h1
        cases h1
      have hnd' : (j :: js).Nodup := List.nodup_cons.mpr ⟨hj_not_mem, hnd⟩
      have hw_rk : rk (js.toFinset ∪ u) = rk u :=
        hrk_union_closed js.toFinset u (fun i hi => hu_cl i (List.mem_toFinset.mp hi))
      have hw_true : f (js.toFinset ∪ u) j = true := by
        rw [hf_true, hw_rk]
        have hlt : rk u < rk (insert j u) := (hf_true u j).mp huj
        have hle : rk (insert j u) ≤ rk (insert j (js.toFinset ∪ u)) :=
          hmono (Finset.insert_subset_insert j Finset.subset_union_right)
        exact lt_of_lt_of_le hlt hle
      have hjs_true : f js.toFinset j = true :=
        h_anti js.toFinset (js.toFinset ∪ u) Finset.subset_union_left j hw_true
      have hrk' : rk (j :: js).toFinset = (j :: js).length := by
        rw [List.toFinset_cons, hrk_ins_succ js.toFinset j hjs_true, hrk_js, List.length_cons]
      have hle_y : (j :: js).length ≤ rk y := by
        have hcl_y : rk ((j :: js).toFinset ∪ y) = rk y :=
          hrk_union_closed (j :: js).toFinset y (fun i hi => hy_cl i (List.mem_toFinset.mp hi))
        rw [← hrk', ← hcl_y]
        exact hmono Finset.subset_union_left
      exact ⟨hy_cl, hnd', hrk', hle_y⟩
  have h_named_of_indep : ∀ js x, (∀ j ∈ js, j ∈ x) → js.Nodup → rk js.toFinset = js.length →
      named js x := by
    intro js
    induction js with
    | nil => intro x _ _ _; trivial
    | cons j js ih =>
      intro x hx hnd hrk
      rcases List.nodup_cons.mp hnd with ⟨hj_not, hnd'⟩
      have hsub_js : ∀ i ∈ js, i ∈ js.toFinset := fun i hi => List.mem_toFinset.mpr hi
      have hrk_js_le : rk js.toFinset ≤ js.length := by
        have h1 := hcard js.toFinset
        have h2 : js.toFinset.card = js.length := List.toFinset_card_of_nodup hnd'
        exact h1.trans h2.le
      have hrk_ins : rk (insert j js.toFinset) = js.length + 1 := by
        simpa [List.toFinset_cons, List.length_cons] using hrk
      have hrk_le_succ := hrk_ins_le js.toFinset j
      have hrk_js : rk js.toFinset = js.length := by linarith
      refine ⟨js.toFinset, insert j js.toFinset, ih js.toFinset hsub_js hnd' hrk_js,
        Finset.subset_insert j js.toFinset, ?_, ?_, ?_⟩
      · intro a ha
        simp only [Finset.mem_insert, List.mem_toFinset] at ha
        rcases ha with rfl | ha
        · exact hx a (List.mem_cons_self ..)
        · exact hx a (List.mem_cons_of_mem j ha)
      · rw [hf_true, hrk_ins, hrk_js]; exact Nat.lt_succ_self _
      · rw [hf_false, Finset.insert_eq_of_mem (Finset.mem_insert_self j js.toFinset)]
  have h_indep_exists : ∀ x k, k ≤ rk x →
      ∃ s : Finset (Fin n), s ⊆ x ∧ s.card = k ∧ rk s = k := by
    intro x k
    induction k with
    | zero =>
      intro _
      exact ⟨∅, Finset.empty_subset x, rfl, h0⟩
    | succ k ih =>
      intro hk
      rcases ih (Nat.le_of_succ_le hk) with ⟨s, hsx, hscard, hsrk⟩
      have hex : ∃ j ∈ x, f s j = true := by
        by_contra hall
        push Not at hall
        have hcl : ∀ j ∈ x, f s j = false := by
          intro j hj
          cases hfj : f s j
          · rfl
          · exact absurd hfj (hall j hj)
        have hu : rk (x ∪ s) = rk s := hrk_union_closed x s hcl
        have hxs : x ∪ s = x := Finset.union_eq_left.mpr hsx
        rw [hxs] at hu
        linarith
      rcases hex with ⟨j, hjx, hfj⟩
      have hj_not : j ∉ s := by
        intro hjs
        have h1 := (hf_true s j).mp hfj
        rw [Finset.insert_eq_of_mem hjs] at h1
        exact Nat.lt_irrefl _ h1
      refine ⟨insert j s, Finset.insert_subset hjx hsx, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hj_not, hscard]
      · rw [hrk_ins_succ s j hfj, hsrk]
  refine ⟨h_anti, ?_, ?_, ?_⟩
  · intro x k
    constructor
    · rintro ⟨js, rfl, hjs⟩
      exact (h_named_inv js x hjs).2.2.2
    · intro hk
      rcases h_indep_exists x k hk with ⟨s, hsx, hscard, hsrk⟩
      refine ⟨s.toList, ?_, ?_⟩
      · rw [Finset.length_toList, hscard]
      · apply h_named_of_indep s.toList x
        · intro j hj; exact hsx (Finset.mem_toList.mp hj)
        · exact Finset.nodup_toList s
        · rw [Finset.toList_toFinset, Finset.length_toList, hsrk, hscard]
  · intro x js hx
    constructor
    · intro hjs
      rcases h_named_inv js x hjs with ⟨_, hnd, hrk, _⟩
      exact ⟨hnd, hrk⟩
    · rintro ⟨hnd, hrk⟩
      exact h_named_of_indep js x hx hnd hrk
  · intro H
    set neigh : Fin n → Finset (Fin n) := fun j => (Finset.univ : Finset (Fin n)).filter (fun i => H i j)
    constructor
    · rintro ⟨h1, _⟩ j
      have hfj : f (neigh j) j = true := h1 (neigh j) j (fun i hi => (Finset.mem_filter.mp hi).2)
      exact (hf_true (neigh j) j).mp hfj
    · intro h
      refine ⟨?_, ?_⟩
      · intro x j hx
        have hsub_n : x ⊆ neigh j := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx i hi⟩
        exact h_anti x (neigh j) hsub_n j ((hf_true (neigh j) j).mpr (h j))
      · intro x j hj
        rw [hf_false, Finset.insert_eq_of_mem hj]
