import Mathlib.Data.Fintype.Card

namespace PEqualNP.Outside.L_lib_693

private def colSet {q : Nat} (T : Fin (q + 3) → Fin q → Fin q) (j a : Fin q) :
    Finset (Fin (q + 3)) :=
  Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)

private lemma exists_inj_of_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : Finset α) : ∀ (J : Finset β), R.card ≤ J.card → ∃ g : R → J, Function.Injective g := by
  refine Finset.induction_on R ?_ ?_
  · intro J _
    exact ⟨fun ⟨x, hx⟩ => False.elim (by simp at hx),
      fun ⟨x, hx⟩ _ => False.elim (by simp at hx)⟩
  · intro a s ha ih J hcard
    have hcs : (insert a s).card = s.card + 1 := by simp [ha]
    have hJpos : 0 < J.card := by omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hJpos
    have hJb : (J.erase b).card + 1 = J.card := Finset.card_erase_add_one hb
    have hle : s.card ≤ (J.erase b).card := by omega
    obtain ⟨g, hg⟩ := ih (J.erase b) hle
    let f : ↥(insert a s) → ↥J := fun r =>
      if hr : r.1 = a then ⟨b, hb⟩
      else
        let r' : ↥s := ⟨r.1, (Finset.mem_insert.mp r.2).resolve_left hr⟩
        ⟨(g r').1, Finset.mem_of_mem_erase (g r').2⟩
    refine ⟨f, ?_⟩
    intro r1 r2 hf
    by_cases h1 : r1.1 = a
    · by_cases h2 : r2.1 = a
      · exact Subtype.ext (h1.trans h2.symm)
      · have hval : (f r1).1 = (f r2).1 := congrArg Subtype.val hf
        simp only [f, h1, h2, ↓reduceDIte] at hval
        exact absurd hval.symm (Finset.ne_of_mem_erase (g _).2)
    · by_cases h2 : r2.1 = a
      · have hval : (f r1).1 = (f r2).1 := congrArg Subtype.val hf
        simp only [f, h1, h2, ↓reduceDIte] at hval
        exact absurd hval (Finset.ne_of_mem_erase (g _).2)
      · have hval : (f r1).1 = (f r2).1 := congrArg Subtype.val hf
        simp only [f, h1, h2, ↓reduceDIte] at hval
        have hgeq : g ⟨r1.1, (Finset.mem_insert.mp r1.2).resolve_left h1⟩ =
            g ⟨r2.1, (Finset.mem_insert.mp r2.2).resolve_left h2⟩ :=
          Subtype.ext hval
        have hreq := hg hgeq
        exact Subtype.ext (congrArg (Subtype.val : ↥s → α) hreq)

private lemma exists_hitting_of_surplus {q : Nat} (T : Fin (q + 3) → Fin q → Fin q)
    (C : Finset (Fin q)) (x0 : Fin q → Fin q)
    (hsurp : C.card + 3 ≤
      (Finset.univ.filter (fun r : Fin (q + 3) => ∃ j ∈ C, T r j = x0 j)).card) :
    ∃ x : Fin q → Fin q, ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j := by
  classical
  set U : Finset (Fin (q + 3)) :=
    Finset.univ.filter (fun r : Fin (q + 3) => ∃ j ∈ C, T r j = x0 j)
  set R : Finset (Fin (q + 3)) := Finset.univ \ U
  set J : Finset (Fin q) := Finset.univ \ C
  have hR : R.card + U.card = q + 3 := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)
    simpa [R] using h
  have hJ : J.card + C.card = q := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    simpa [J] using h
  have hle : R.card ≤ J.card := by omega
  obtain ⟨g, hg⟩ := exists_inj_of_card_le R J hle
  let x : Fin q → Fin q := fun j =>
    if j ∈ C then x0 j
    else if h : ∃ r : R, (g r).1 = j then T h.choose.1 j
    else x0 j
  refine ⟨x, fun r => ?_⟩
  by_cases hr : r ∈ U
  · have hmem := Finset.mem_filter.mp hr
    obtain ⟨j, hjC, hT⟩ := hmem.2
    exact ⟨j, by simp [x, hjC, hT]⟩
  · let r' : R := ⟨r, by simp [R, hr]⟩
    let j : Fin q := (g r').1
    have hjJ : j ∈ J := (g r').2
    have hjC : j ∉ C := by
      have hmem := Finset.mem_sdiff.mp hjJ
      exact hmem.2
    have hex : ∃ u : R, (g u).1 = j := ⟨r', rfl⟩
    have hchoose : hex.choose = r' := hg (Subtype.ext hex.choose_spec)
    refine ⟨j, ?_⟩
    simp only [x, hjC, hex, ↓reduceIte, ↓reduceDIte]
    rw [hchoose]

private lemma exists_third_of_card_three {α : Type*} [DecidableEq α] {s : Finset α}
    {x y : α} (hcard : s.card = 3) (hxy : x ≠ y) (hx : x ∈ s) (hy : y ∈ s) :
    ∃ e : α, e ≠ x ∧ e ≠ y ∧ s = {x, y, e} := by
  have hsub : ({x, y} : Finset α) ⊆ s := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hsd : (s \ {x, y}).card = 1 := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    have h2 : ({x, y} : Finset α).card = 2 := by simp [hxy]
    omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hsd
  have he_mem : e ∈ s \ {x, y} := by rw [he]; simp
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at he_mem
  refine ⟨e, he_mem.2.1, he_mem.2.2, ?_⟩
  ext z
  have hz : z ∈ s ↔ z ∈ s \ {x, y} ∪ {x, y} := by
    rw [Finset.sdiff_union_of_subset hsub]
  rw [hz, he]
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rintro (rfl | rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

private lemma eq_triple_of_missing {α : Type*} [DecidableEq α] {q : Nat}
    (A : Fin q → Finset α)
    (hcard : ∀ j, (A j).card = 3)
    (hinter : ∀ j1 j2, j1 ≠ j2 → (A j1 ∩ A j2).card = 2)
    {j0 j1 : Fin q} {u v c0 c1 : α}
    (hc0v : c0 ≠ v) (hc1v : c1 ≠ v) (hc01 : c0 ≠ c1)
    (hAj0 : A j0 = {u, v, c0}) (hAj1 : A j1 = {u, v, c1})
    {j : Fin q} (hu : u ∉ A j) : A j = {v, c0, c1} := by
  have hj0 : j ≠ j0 := fun h => hu (by rw [h, hAj0]; simp)
  have hj1 : j ≠ j1 := fun h => hu (by rw [h, hAj1]; simp)
  have hsub0 : A j ∩ A j0 ⊆ {v, c0} := by
    intro z hz
    simp only [Finset.mem_inter, hAj0, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz.2 with rfl | rfl | rfl
    · exact absurd hz.1 hu
    · exact Or.inl rfl
    · exact Or.inr rfl
  have heq0 : A j ∩ A j0 = {v, c0} := by
    refine Finset.eq_of_subset_of_card_le hsub0 ?_
    have h1 : ({v, c0} : Finset α).card ≤ 2 := by
      have := Finset.card_insert_le v ({c0} : Finset α)
      simp at this
      exact this
    have h2 := hinter j j0 hj0
    omega
  have hsub1 : A j ∩ A j1 ⊆ {v, c1} := by
    intro z hz
    simp only [Finset.mem_inter, hAj1, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz.2 with rfl | rfl | rfl
    · exact absurd hz.1 hu
    · exact Or.inl rfl
    · exact Or.inr rfl
  have heq1 : A j ∩ A j1 = {v, c1} := by
    refine Finset.eq_of_subset_of_card_le hsub1 ?_
    have h1 : ({v, c1} : Finset α).card ≤ 2 := by
      have := Finset.card_insert_le v ({c1} : Finset α)
      simp at this
      exact this
    have h2 := hinter j j1 hj1
    omega
  have hv : v ∈ A j := by
    have : v ∈ A j ∩ A j0 := by rw [heq0]; simp
    exact (Finset.mem_inter.mp this).1
  have hc0 : c0 ∈ A j := by
    have : c0 ∈ A j ∩ A j0 := by rw [heq0]; simp
    exact (Finset.mem_inter.mp this).1
  have hc1 : c1 ∈ A j := by
    have : c1 ∈ A j ∩ A j1 := by rw [heq1]; simp
    exact (Finset.mem_inter.mp this).1
  have hsub : ({v, c0, c1} : Finset α) ⊆ A j := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hv
    · exact hc0
    · exact hc1
  have h3 : ({v, c0, c1} : Finset α).card = 3 := by
    simp [hc0v.symm, hc1v.symm, hc01]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [h3, hcard j])).symm

private lemma no_missing_of_pairwise_inter_two {α : Type*} [DecidableEq α] {q : Nat}
    (hq : 5 ≤ q) (A : Fin q → Finset α)
    (hcard : ∀ j, (A j).card = 3)
    (hinj : Function.Injective A)
    (hinter : ∀ j1 j2, j1 ≠ j2 → (A j1 ∩ A j2).card = 2)
    {j0 j1 : Fin q} {x y c0 c1 : α}
    (hxy : x ≠ y) (hc0x : c0 ≠ x) (hc0y : c0 ≠ y)
    (hc1x : c1 ≠ x) (hc1y : c1 ≠ y) (hc01 : c0 ≠ c1)
    (hAj0 : A j0 = {x, y, c0}) (hAj1 : A j1 = {x, y, c1})
    {j2 : Fin q} (hx2 : x ∉ A j2) : False := by
  have hAj0_swap : A j0 = {y, x, c0} := by
    rw [hAj0]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
    · rintro (rfl | rfl | rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr rfl)
  have hAj1_swap : A j1 = {y, x, c1} := by
    rw [hAj1]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
    · rintro (rfl | rfl | rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr rfl)
  have hAj2 : A j2 = {y, c0, c1} :=
    eq_triple_of_missing A hcard hinter hc0y hc1y hc01 hAj0 hAj1 hx2
  let F : Finset (Finset α) := {{y, c0, c1}, {x, c0, c1}, {x, y, c0}, {x, y, c1}}
  have hmemF : ∀ j : Fin q, A j ∈ F := by
    intro j
    by_cases hx : x ∈ A j
    · by_cases hy : y ∈ A j
      · have hj2 : j ≠ j2 := fun h => hx2 (h ▸ hx)
        obtain ⟨e, hex, hey, hAj⟩ := exists_third_of_card_three (hcard j) hxy hx hy
        have hec : e = c0 ∨ e = c1 := by
          refine Classical.byContradiction fun hne => ?_
          have he0 : e ≠ c0 := fun h => hne (Or.inl h)
          have he1 : e ≠ c1 := fun h => hne (Or.inr h)
          have hsub : A j ∩ A j2 ⊆ {y} := by
            intro z hz
            simp only [Finset.mem_inter, hAj, hAj2, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
            rcases hz.1 with rfl | rfl | rfl
            · rcases hz.2 with h | h | h
              · exact absurd h hxy
              · exact absurd h.symm hc0x
              · exact absurd h.symm hc1x
            · rfl
            · rcases hz.2 with h | h | h
              · exact absurd h hey
              · exact absurd h he0
              · exact absurd h he1
          have hle := Finset.card_le_card hsub
          have h2 := hinter j j2 hj2
          simp at hle
          omega
        rcases hec with rfl | rfl
        · simp [F, hAj]
        · simp [F, hAj]
      · have hAj : A j = {x, c0, c1} :=
          eq_triple_of_missing A hcard hinter hc0x hc1x hc01 hAj0_swap hAj1_swap hy
        simp [F, hAj]
    · have hAj : A j = {y, c0, c1} :=
        eq_triple_of_missing A hcard hinter hc0y hc1y hc01 hAj0 hAj1 hx
      simp [F, hAj]
  have hle : (Finset.univ : Finset (Fin q)).card ≤ F.card :=
    Finset.card_le_card_of_injOn A (fun j _ => hmemF j) (fun _ _ _ _ h => hinj h)
  have hF : F.card ≤ 4 := by
    have h1 := Finset.card_insert_le ({y, c0, c1} : Finset α) {{x, c0, c1}, {x, y, c0}, {x, y, c1}}
    have h2 := Finset.card_insert_le ({x, c0, c1} : Finset α) {{x, y, c0}, {x, y, c1}}
    have h3 := Finset.card_insert_le ({x, y, c0} : Finset α) {{x, y, c1}}
    simp only [Finset.card_singleton] at h3
    dsimp only [F]
    omega
  simp only [Finset.card_univ, Fintype.card_fin] at hle
  omega

private lemma main_proof (q : Nat) (T : Fin (q + 3) → Fin q → Fin q) (hq : 7 ≤ q)
    (h3 : ∀ j : Fin q, ∃ a : Fin q,
      3 ≤ (Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)).card) :
    ∃ x : Fin q → Fin q, ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j := by
  classical
  refine Classical.byContradiction fun hno => ?_
  have hsurp : ∀ (C : Finset (Fin q)) (x0 : Fin q → Fin q),
      (Finset.univ.filter (fun r : Fin (q + 3) => ∃ j ∈ C, T r j = x0 j)).card < C.card + 3 := by
    intro C x0
    refine Classical.byContradiction fun hle => hno ?_
    exact exists_hitting_of_surplus T C x0 (by omega)
  have hcol : ∀ (j a : Fin q), (colSet T j a).card ≤ 3 := by
    intro j a
    have h1 := hsurp {j} (fun _ => a)
    have heq : Finset.univ.filter (fun r : Fin (q + 3) =>
        ∃ k ∈ ({j} : Finset (Fin q)), T r k = a) = colSet T j a := by
      ext r
      simp [colSet]
    rw [heq, Finset.card_singleton] at h1
    omega
  have hpair : ∀ (j1 j2 a1 a2 : Fin q), j1 ≠ j2 →
      (colSet T j1 a1 ∪ colSet T j2 a2).card ≤ 4 := by
    intro j1 j2 a1 a2 hne
    have h1 := hsurp {j1, j2} (fun j => if j = j1 then a1 else a2)
    have h2 : ({j1, j2} : Finset (Fin q)).card = 2 := by simp [hne]
    have heq : Finset.univ.filter (fun r : Fin (q + 3) =>
        ∃ k ∈ ({j1, j2} : Finset (Fin q)), T r k = (if k = j1 then a1 else a2)) =
        colSet T j1 a1 ∪ colSet T j2 a2 := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton, colSet]
      constructor
      · rintro ⟨k, rfl | rfl, hk⟩
        · left; simpa using hk
        · right; simpa [hne.symm] using hk
      · rintro (h | h)
        · exact ⟨j1, Or.inl rfl, by simpa using h⟩
        · exact ⟨j2, Or.inr rfl, by simpa [hne.symm] using h⟩
    rw [heq, h2] at h1
    omega
  let a : Fin q → Fin q := fun j => (h3 j).choose
  let A : Fin q → Finset (Fin (q + 3)) := fun j => colSet T j (a j)
  have hA_card : ∀ j : Fin q, (A j).card = 3 := by
    intro j
    have hge : 3 ≤ (A j).card := (h3 j).choose_spec
    have hle : (A j).card ≤ 3 := hcol j (a j)
    omega
  have hex_pair : ∀ j : Fin q, ∃ (b : Fin q) (u v : Fin (q + 3)),
      u ≠ v ∧ u ∉ A j ∧ v ∉ A j ∧ T u j = b ∧ T v j = b := by
    intro j
    let R : Finset (Fin (q + 3)) := Finset.univ \ A j
    let V : Finset (Fin q) := Finset.univ.erase (a j)
    have hR : R.card = q := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A j))
      simp only [Finset.card_univ, Fintype.card_fin, hA_card j] at h
      dsimp only [R]
      omega
    have hV : V.card + 1 = q := by
      have h := Finset.card_erase_add_one (Finset.mem_univ (a j))
      simpa [V] using h
    have hlt : V.card < R.card := by omega
    have hmaps : ∀ r ∈ R, T r j ∈ V := by
      intro r hr
      simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and, A, colSet,
        Finset.mem_filter] at hr
      simp [V, hr]
    obtain ⟨u, hu, v, hv, huv, hTuv⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
    exact ⟨T u j, u, v, huv, (Finset.mem_sdiff.mp hu).2, (Finset.mem_sdiff.mp hv).2,
      rfl, hTuv.symm⟩
  have hA_inj : Function.Injective A := by
    intro j1 j2 heq
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨b, u, v, huv, hu2, hv2, hTu, hTv⟩ := hex_pair j2
    have hu1 : u ∉ A j1 := by rw [heq]; exact hu2
    have hv1 : v ∉ A j1 := by rw [heq]; exact hv2
    have hdisj : Disjoint (A j1) ({u, v} : Finset (Fin (q + 3))) := by
      rw [Finset.disjoint_right]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hu1
      · exact hv1
    have hsub : A j1 ∪ {u, v} ⊆ colSet T j1 (a j1) ∪ colSet T j2 b := by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
      rcases hz with hz | rfl | rfl
      · exact Or.inl hz
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTu⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTv⟩)
    have h5 : (A j1 ∪ {u, v}).card = 5 := by
      rw [Finset.card_union_of_disjoint hdisj, hA_card j1]
      have h2 : ({u, v} : Finset (Fin (q + 3))).card = 2 := by simp [huv]
      omega
    have hle := Finset.card_le_card hsub
    have h4 := hpair j1 j2 (a j1) b hne
    omega
  have hA_inter : ∀ j1 j2 : Fin q, j1 ≠ j2 → (A j1 ∩ A j2).card = 2 := by
    intro j1 j2 hne
    have hinc := Finset.card_union_add_card_inter (A j1) (A j2)
    have h4 : (A j1 ∪ A j2).card ≤ 4 := hpair j1 j2 (a j1) (a j2) hne
    have hle3 : (A j1 ∩ A j2).card ≤ 3 := by
      have := Finset.card_le_card (Finset.inter_subset_left (s₁ := A j1) (s₂ := A j2))
      rw [hA_card j1] at this
      exact this
    have hne3 : (A j1 ∩ A j2).card ≠ 3 := by
      intro h3i
      have h1 : A j1 ∩ A j2 = A j1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h3i, hA_card j1])
      have h2 : A j1 ∩ A j2 = A j2 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h3i, hA_card j2])
      exact hne (hA_inj (h1.symm.trans h2))
    rw [hA_card j1, hA_card j2] at hinc
    omega
  let j0 : Fin q := ⟨0, by omega⟩
  let j1 : Fin q := ⟨1, by omega⟩
  have hj01 : j0 ≠ j1 := by
    intro h
    have := congrArg Fin.val h
    simp [j0, j1] at this
  obtain ⟨p0, p1, hp01, hinter01⟩ := Finset.card_eq_two.mp (hA_inter j0 j1 hj01)
  have hp0_j0 : p0 ∈ A j0 := (Finset.mem_inter.mp (by rw [hinter01]; simp)).1
  have hp1_j0 : p1 ∈ A j0 := (Finset.mem_inter.mp (by rw [hinter01]; simp)).1
  have hp0_j1 : p0 ∈ A j1 := (Finset.mem_inter.mp (by rw [hinter01]; simp)).2
  have hp1_j1 : p1 ∈ A j1 := (Finset.mem_inter.mp (by rw [hinter01]; simp)).2
  obtain ⟨c0, hc00, hc01p, hAj0⟩ := exists_third_of_card_three (hA_card j0) hp01 hp0_j0 hp1_j0
  obtain ⟨c1, hc10, hc11p, hAj1⟩ := exists_third_of_card_three (hA_card j1) hp01 hp0_j1 hp1_j1
  have hc01 : c0 ≠ c1 := by
    intro h
    apply hj01
    apply hA_inj
    rw [hAj0, hAj1, h]
  have hcommon : ∀ j : Fin q, p0 ∈ A j ∧ p1 ∈ A j := by
    intro j
    constructor
    · refine Classical.byContradiction fun hnp0 => ?_
      exact no_missing_of_pairwise_inter_two (by omega) A hA_card hA_inj hA_inter
        hp01 hc00 hc01p hc10 hc11p hc01 hAj0 hAj1 hnp0
    · refine Classical.byContradiction fun hnp1 => ?_
      have hAj0s : A j0 = {p1, p0, c0} := by
        rw [hAj0]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
        · rintro (rfl | rfl | rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr rfl)
        · rintro (rfl | rfl | rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr rfl)
      have hAj1s : A j1 = {p1, p0, c1} := by
        rw [hAj1]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; constructor
        · rintro (rfl | rfl | rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr rfl)
        · rintro (rfl | rfl | rfl); exact Or.inr (Or.inl rfl); exact Or.inl rfl; exact Or.inr (Or.inr rfl)
      exact no_missing_of_pairwise_inter_two (by omega) A hA_card hA_inj hA_inter
        hp01.symm hc01p hc00 hc11p hc10 hc01 hAj0s hAj1s hnp1
  have hthird : ∀ j : Fin q, ∃ e : Fin (q + 3), e ≠ p0 ∧ e ≠ p1 ∧ A j = {p0, p1, e} :=
    fun j => exists_third_of_card_three (hA_card j) hp01 (hcommon j).1 (hcommon j).2
  let c : Fin q → Fin (q + 3) := fun j => (hthird j).choose
  have hc_eq : ∀ j : Fin q, A j = {p0, p1, c j} := fun j => (hthird j).choose_spec.2.2
  have hc_inj : Function.Injective c := by
    intro j1' j2' hceq
    apply hA_inj
    rw [hc_eq j1', hc_eq j2', hceq]
  obtain ⟨b0, u, v, huv, hu0, hv0, hTu, hTv⟩ := hex_pair j0
  have hup0 : u ≠ p0 := fun h => hu0 (h ▸ (hcommon j0).1)
  have hup1 : u ≠ p1 := fun h => hu0 (h ▸ (hcommon j0).2)
  have hvp0 : v ≠ p0 := fun h => hv0 (h ▸ (hcommon j0).1)
  have hvp1 : v ≠ p1 := fun h => hv0 (h ▸ (hcommon j0).2)
  let Bu : Finset (Fin q) := Finset.univ.filter (fun j => c j = u)
  let Bv : Finset (Fin q) := Finset.univ.filter (fun j => c j = v)
  let B : Finset (Fin q) := {j0} ∪ Bu ∪ Bv
  have hBu : Bu.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Bu, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hc_inj (hx.trans hy.symm)
  have hBv : Bv.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Bv, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hc_inj (hx.trans hy.symm)
  have hB : B.card ≤ 3 := by
    have h1 := Finset.card_union_le ({j0} ∪ Bu) Bv
    have h2 := Finset.card_union_le ({j0} : Finset (Fin q)) Bu
    simp only [Finset.card_singleton] at h2
    dsimp only [B]
    omega
  have hdiff : 0 < ((Finset.univ : Finset (Fin q)) \ B).card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  obtain ⟨j', hj'⟩ := Finset.card_pos.mp hdiff
  have hj'B : j' ∉ B := (Finset.mem_sdiff.mp hj').2
  have hj'_ne : j' ≠ j0 := fun h => hj'B (by simp [B, h])
  have hcj'_u : c j' ≠ u := fun h => hj'B (by simp [B, Bu, h])
  have hcj'_v : c j' ≠ v := fun h => hj'B (by simp [B, Bv, h])
  have hdisj : Disjoint (A j') ({u, v} : Finset (Fin (q + 3))) := by
    rw [Finset.disjoint_right]
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [hc_eq j']
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    rcases hz with rfl | rfl
    · exact ⟨hup0, hup1, hcj'_u.symm⟩
    · exact ⟨hvp0, hvp1, hcj'_v.symm⟩
  have hsub : A j' ∪ {u, v} ⊆ colSet T j' (a j') ∪ colSet T j0 b0 := by
    intro z hz
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with hz | rfl | rfl
    · exact Or.inl hz
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTu⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTv⟩)
  have h5 : (A j' ∪ {u, v}).card = 5 := by
    rw [Finset.card_union_of_disjoint hdisj, hA_card j']
    have h2 : ({u, v} : Finset (Fin (q + 3))).card = 2 := by simp [huv]
    omega
  have hle := Finset.card_le_card hsub
  have h4 := hpair j' j0 (a j') b0 hj'_ne
  omega

end PEqualNP.Outside.L_lib_693

theorem PEqualNP.Outside.L_lib_693 :
    ∀ (q : Nat) (T : Fin (q + 3) → Fin q → Fin q), 7 ≤ q →
      (∀ j : Fin q, ∃ a : Fin q,
        3 ≤ (Finset.univ.filter (fun r : Fin (q + 3) => T r j = a)).card) →
      ∃ x : Fin q → Fin q, ∀ r : Fin (q + 3), ∃ j : Fin q, T r j = x j :=
  PEqualNP.Outside.L_lib_693.main_proof
