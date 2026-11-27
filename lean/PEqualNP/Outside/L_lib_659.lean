import Mathlib

namespace PEqualNP.Outside.L_lib_659

private noncomputable def cylinder {n : Nat} (s p : Finset (Fin n)) :
    Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (fun x => x ∩ s = p)

private lemma mem_cylinder {n : Nat} {s p x : Finset (Fin n)} :
    x ∈ cylinder s p ↔ x ∩ s = p := by
  classical
  simp [cylinder]

private def weight (n m : Nat) : Nat := 2 ^ (n - m)

private lemma card_cylinder {n : Nat} {s p : Finset (Fin n)} (h : p ⊆ s) :
    (cylinder s p).card = weight n s.card := by
  classical
  let f : Finset (Fin n) → Finset (Fin n) := fun x => x \ s
  have hcard : (cylinder s p).card = ((Finset.univ \ s).powerset).card := by
    refine Finset.card_bij (fun x _ => f x) ?_ ?_ ?_
    · intro x _
      rw [Finset.mem_powerset]
      intro z hz
      simp only [f, Finset.mem_sdiff, Finset.mem_univ, true_and] at hz ⊢
      exact hz.2
    · intro x hx y hy heq
      have hx' := mem_cylinder.mp hx
      have hy' := mem_cylinder.mp hy
      ext z
      have hz := Finset.ext_iff.mp heq z
      have hp : z ∈ x ∩ s ↔ z ∈ y ∩ s := by rw [hx', hy']
      simp only [f, Finset.mem_sdiff, Finset.mem_inter] at hz hp
      by_cases hs : z ∈ s <;> simp_all
    · intro a ha
      rw [Finset.mem_powerset] at ha
      have hs : ∀ z ∈ a, z ∉ s := fun z hz => (Finset.mem_sdiff.mp (ha hz)).2
      refine ⟨a ∪ p, mem_cylinder.mpr ?_, ?_⟩
      · ext z
        simp only [Finset.mem_union, Finset.mem_inter]
        exact ⟨fun ⟨hza, hzs⟩ => hza.resolve_left (fun h' => hs z h' hzs),
          fun hzp => ⟨Or.inr hzp, h hzp⟩⟩
      · ext z
        simp only [f, Finset.mem_sdiff, Finset.mem_union]
        exact ⟨fun ⟨hza, hzs⟩ => hza.resolve_right (fun hp => hzs (h hp)),
          fun hza => ⟨Or.inl hza, hs z hza⟩⟩
  rw [hcard, Finset.card_powerset, Finset.card_sdiff_of_subset (Finset.subset_univ s)]
  simp [weight]

private noncomputable def cell {n : Nat} (s y : Finset (Fin n)) :
    Finset (Finset (Fin n)) := cylinder s (y ∩ s)

private lemma cell_inter {n : Nat} (a b y : Finset (Fin n)) :
    cell a y ∩ cell b y = cell (a ∪ b) y := by
  classical
  ext x
  simp only [Finset.mem_inter, cell, mem_cylinder, Finset.ext_iff, Finset.mem_union]
  aesop

private lemma card_cell {n : Nat} (a y : Finset (Fin n)) :
    (cell a y).card = weight n a.card := card_cylinder Finset.inter_subset_right

private lemma triple_cards {α : Type*} [DecidableEq α] (a b c : Finset α) :
    (a ∪ b ∪ c).card + (a ∩ b).card + (a ∩ c).card + (b ∩ c).card =
      a.card + b.card + c.card + (a ∩ b ∩ c).card := by
  have h₁ := Finset.card_union_add_card_inter a b
  have h₂ := Finset.card_union_add_card_inter (a ∪ b) c
  have h₃ := Finset.card_union_add_card_inter (a ∩ c) (b ∩ c)
  have hu : (a ∪ b) ∩ c = (a ∩ c) ∪ (b ∩ c) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have hi : (a ∩ c) ∩ (b ∩ c) = a ∩ b ∩ c := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  rw [hu] at h₂
  rw [hi] at h₃
  omega

private lemma distinct_union {α : Type*} [DecidableEq α] {a b : Finset α} {k : Nat}
    (ha : a.card = k) (hb : b.card = k) (hne : a ≠ b) : k + 1 ≤ (a ∪ b).card := by
  by_contra! h
  have h₁ : a = a ∪ b := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have h₂ : b = a ∪ b := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  exact hne (h₁.trans h₂.symm)

private lemma shared_union {α : Type*} [DecidableEq α] (a b c : Finset α) (k : Nat)
    (ha : a.card = k) (hab : (a ∪ b).card = k + 1) (hac : (a ∪ c).card = k + 1) :
    (a ∪ b ∪ c).card ≤ k + 2 := by
  have hm := Finset.card_union_add_card_inter (a ∪ b) (a ∪ c)
  have hu : (a ∪ b) ∪ (a ∪ c) = a ∪ b ∪ c := by
    ext x
    simp only [Finset.mem_union]
    tauto
  have hi : a ⊆ (a ∪ b) ∩ (a ∪ c) := fun _ hx =>
    Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hx, Finset.mem_union_left _ hx⟩
  have hle := Finset.card_le_card hi
  rw [hu] at hm
  omega

private lemma core_criterion {α : Type*} [DecidableEq α] (a b c : Finset α) (k : Nat)
    (ha : a.card = k) (hb : b.card = k) (hc : c.card = k)
    (hab : k + 1 ≤ (a ∪ b).card) (hac : k + 1 ≤ (a ∪ c).card)
    (hbc : k + 1 ≤ (b ∪ c).card) :
    ((a ∪ b ∪ c).card = k + 2 ∧ (a ∪ b).card = k + 1 ∧
      (a ∪ c).card = k + 1 ∧ (b ∪ c).card = k + 1) ↔
      (a ∩ b ∩ c).card + 1 = k := by
  have h₁ := Finset.card_union_add_card_inter a b
  have h₂ := Finset.card_union_add_card_inter a c
  have h₃ := Finset.card_union_add_card_inter b c
  have h₄ := triple_cards a b c
  constructor
  · rintro ⟨ht, h₅, h₆, h₇⟩
    omega
  · intro hcore
    have hs₁ : a ∩ b ∩ c ⊆ a ∩ b := Finset.inter_subset_left
    have hs₂ : a ∩ b ∩ c ⊆ a ∩ c := fun _ hx =>
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1,
        (Finset.mem_inter.mp hx).2⟩
    have hs₃ : a ∩ b ∩ c ⊆ b ∩ c := fun _ hx =>
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2,
        (Finset.mem_inter.mp hx).2⟩
    have h₅ := Finset.card_le_card hs₁
    have h₆ := Finset.card_le_card hs₂
    have h₇ := Finset.card_le_card hs₃
    exact ⟨by omega, by omega, by omega, by omega⟩

private lemma weight_mul {n a b : Nat} (hab : a ≤ b) (hbn : b ≤ n) :
    2 ^ (b - a) * weight n b = weight n a := by
  unfold weight
  rw [← pow_add]
  congr 1
  omega

private lemma weight_le {n a b : Nat} (hab : a ≤ b) :
    weight n b ≤ weight n a :=
  Nat.pow_le_pow_right (by decide) (by omega)

private lemma weight_threshold (n k i j l t r : Nat)
    (hi : k + 1 ≤ i) (hj : k + 1 ≤ j) (hl : k + 1 ≤ l)
    (hit : i ≤ t) (hjt : j ≤ t) (hlt : l ≤ t) (htn : t ≤ n)
    (hpair : (i = k + 1 ∧ j = k + 1 ∨ i = k + 1 ∧ l = k + 1 ∨
      j = k + 1 ∧ l = k + 1) → t ≤ k + 2)
    (hcount : r + weight n i + weight n j + weight n l =
      3 * weight n k + weight n t) :
    (r < 2 * weight n k ↔
      t = k + 2 ∧ i = k + 1 ∧ j = k + 1 ∧ l = k + 1) ∧
      (r < 2 * weight n k → 4 * r = 7 * weight n k) := by
  have hpos : 0 < weight n t := Nat.pow_pos (by decide)
  obtain ht | ht | ht : t = k + 1 ∨ t = k + 2 ∨ k + 3 ≤ t := by omega
  · have hw : 2 * weight n t = weight n k := by
      simpa [show t - k = 1 by omega] using
        weight_mul (a := k) (b := t) (by omega) htn
    have h₁ : i = t := by omega
    have h₂ : j = t := by omega
    have h₃ : l = t := by omega
    rw [h₁, h₂, h₃] at hcount
    omega
  · have hw : 4 * weight n t = weight n k := by
      simpa [show t - k = 2 by omega] using
        weight_mul (a := k) (b := t) (by omega) htn
    have exact_weight (m : Nat) (hm : k + 1 ≤ m) (hmt : m ≤ t) :
        (m = k + 1 ∧ weight n m = 2 * weight n t) ∨
        (m = k + 2 ∧ weight n m = weight n t) := by
      by_cases heq : m = k + 1
      · refine Or.inl ⟨heq, ?_⟩
        simpa [show t - m = 1 by omega] using (weight_mul hmt htn).symm
      · have heq' : m = t := by omega
        exact Or.inr ⟨by omega, congrArg (weight n) heq'⟩
    rcases exact_weight i hi hit with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases exact_weight j hj hjt with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases exact_weight l hl hlt with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
  · have hno : ¬ (i = k + 1 ∧ j = k + 1 ∨ i = k + 1 ∧ l = k + 1 ∨
        j = k + 1 ∧ l = k + 1) := fun h => by have := hpair h; omega
    have hw₁ : 2 * weight n (k + 1) = weight n k := by
      simpa using weight_mul (a := k) (b := k + 1) (by omega) (show k + 1 ≤ n by omega)
    have hw₂ : 4 * weight n (k + 2) = weight n k := by
      simpa [show k + 2 - k = 2 by omega] using
        weight_mul (a := k) (b := k + 2) (by omega) (show k + 2 ≤ n by omega)
    have small (m : Nat) (hm : k + 1 ≤ m) : 2 * weight n m ≤ weight n k := by
      have h := weight_le (n := n) hm
      omega
    have large (m : Nat) (hm : k + 1 ≤ m) (hne : m ≠ k + 1) :
        4 * weight n m ≤ weight n k := by
      have h := weight_le (n := n) (show k + 2 ≤ m by omega)
      omega
    by_cases h₁ : i = k + 1
    · have h₂ : j ≠ k + 1 := by tauto
      have h₃ : l ≠ k + 1 := by tauto
      have := small i hi
      have := large j hj h₂
      have := large l hl h₃
      omega
    · have := large i hi h₁
      by_cases h₂ : j = k + 1
      · have h₃ : l ≠ k + 1 := by tauto
        have := small j hj
        have := large l hl h₃
        omega
      · have := large j hj h₂
        have := small l hl
        omega

private lemma compatible {n k : Nat} (a b c y : Finset (Fin n))
    (ha : a.card = k) (hb : b.card = k) (hc : c.card = k)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let r := (cell a y ∪ cell b y ∪ cell c y).card
    (r < 2 * weight n k ↔ (a ∩ b ∩ c).card + 1 = k) ∧
      (r < 2 * weight n k → 4 * r = 7 * weight n k) := by
  dsimp only
  have h₁ := distinct_union ha hb hab
  have h₂ := distinct_union ha hc hac
  have h₃ := distinct_union hb hc hbc
  have hu₁ : a ∪ b ⊆ a ∪ b ∪ c := Finset.subset_union_left
  have hu₂ : a ∪ c ⊆ a ∪ b ∪ c := by
    intro x hx
    simp only [Finset.mem_union] at hx ⊢
    tauto
  have hu₃ : b ∪ c ⊆ a ∪ b ∪ c := by
    intro x hx
    simp only [Finset.mem_union] at hx ⊢
    tauto
  have hn : (a ∪ b ∪ c).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (a ∪ b ∪ c))
  have hpair : ((a ∪ b).card = k + 1 ∧ (a ∪ c).card = k + 1 ∨
        (a ∪ b).card = k + 1 ∧ (b ∪ c).card = k + 1 ∨
        (a ∪ c).card = k + 1 ∧ (b ∪ c).card = k + 1) → (a ∪ b ∪ c).card ≤ k + 2 := by
    rintro (⟨he, hf⟩ | ⟨he, hf⟩ | ⟨he, hf⟩)
    · exact shared_union a b c k ha he hf
    · have he' : (b ∪ a).card = k + 1 := by simpa only [Finset.union_comm] using he
      simpa only [Finset.union_comm] using shared_union b a c k hb he' hf
    · have he' : (c ∪ a).card = k + 1 := by simpa only [Finset.union_comm] using he
      have hf' : (c ∪ b).card = k + 1 := by simpa only [Finset.union_comm] using hf
      have hperm : c ∪ a ∪ b = a ∪ b ∪ c := by
        ext x
        simp only [Finset.mem_union]
        tauto
      simpa only [hperm] using shared_union c a b k hc he' hf'
  have hcount := triple_cards (cell a y) (cell b y) (cell c y)
  simp only [cell_inter, card_cell, ha, hb, hc] at hcount
  have hr := weight_threshold n k _ _ _ _ (cell a y ∪ cell b y ∪ cell c y).card h₁ h₂ h₃
    (Finset.card_le_card hu₁) (Finset.card_le_card hu₂) (Finset.card_le_card hu₃)
    hn hpair (by omega)
  exact ⟨hr.1.trans (core_criterion a b c k ha hb hc h₁ h₂ h₃), hr.2⟩

private lemma glue {n : Nat} {scope pat : Fin 3 → Finset (Fin n)}
    (hsub : ∀ i, pat i ⊆ scope i)
    (hpair : ∀ i j, ¬ Disjoint (cylinder (scope i) (pat i)) (cylinder (scope j) (pat j))) :
    ∃ y : Finset (Fin n), ∀ i, y ∩ scope i = pat i := by
  classical
  have hp (i j : Fin 3) : ∃ x, x ∩ scope i = pat i ∧ x ∩ scope j = pat j := by
    by_contra! hnone
    exact hpair i j (Finset.disjoint_left.mpr fun _ hi hj =>
      hnone _ (mem_cylinder.mp hi) (mem_cylinder.mp hj))
  refine ⟨Finset.univ.biUnion pat, fun i => ?_⟩
  ext v
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j, hv⟩, hvs⟩
    obtain ⟨x, hi, hj⟩ := hp i j
    rw [← hj, Finset.mem_inter] at hv
    rw [← hi, Finset.mem_inter]
    exact ⟨hv.1, hvs⟩
  · exact fun hv => ⟨⟨i, hv⟩, hsub i hv⟩

private lemma solve {n k : Nat} (scope pat : Fin 3 → Finset (Fin n))
    (hsize : ∀ i, (scope i).card = k ∧ pat i ⊆ scope i)
    (hinj : Function.Injective (fun i : Fin 3 => (scope i, pat i))) :
    let u := 2^(n-k)
    let covered := ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun x => ∃ i : Fin 3, x ∩ scope i = pat i)).card
    let core := scope 0 ∩ scope 1 ∩ scope 2
    let consistent := ∃ y : Finset (Fin n), ∀ i : Fin 3, y ∩ scope i = pat i
    (covered < 2*u ↔ consistent ∧ core.card+1 = k) ∧
      (covered < 2*u → 4*covered = 7*u) := by
  dsimp only
  classical
  let cov := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun x => ∃ i : Fin 3, x ∩ scope i = pat i)
  have hcov_def : cov = (Finset.univ : Finset (Finset (Fin n))).filter
      (fun x => ∃ i : Fin 3, x ∩ scope i = pat i) := by
    ext x
    simp [cov]
  rw [← hcov_def]
  by_cases h : ∃ y : Finset (Fin n), ∀ i : Fin 3, y ∩ scope i = pat i
  · obtain ⟨y, hy⟩ := h
    have hscope : Function.Injective scope := by
      intro i j hij
      apply hinj
      refine Prod.ext hij ?_
      change pat i = pat j
      rw [← hy i, ← hy j, hij]
    have hcov : cov = cell (scope 0) y ∪ cell (scope 1) y ∪ cell (scope 2) y := by
      ext x
      simp only [cov, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        cell, mem_cylinder]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl (Or.inl (hi.trans (hy 0).symm))
        · exact Or.inl (Or.inr (hi.trans (hy 1).symm))
        · exact Or.inr (hi.trans (hy 2).symm)
      · rintro ((h₀ | h₁) | h₂)
        · exact ⟨0, h₀.trans (hy 0)⟩
        · exact ⟨1, h₁.trans (hy 1)⟩
        · exact ⟨2, h₂.trans (hy 2)⟩
    have hgood : ∃ y : Finset (Fin n), ∀ i : Fin 3, y ∩ scope i = pat i := ⟨y, hy⟩
    rw [hcov]
    simp only [hgood, true_and]
    exact compatible (scope 0) (scope 1) (scope 2) y
      (hsize 0).1 (hsize 1).1 (hsize 2).1
      (fun he => (by decide : (0 : Fin 3) ≠ 1) (hscope he))
      (fun he => (by decide : (0 : Fin 3) ≠ 2) (hscope he))
      (fun he => (by decide : (1 : Fin 3) ≠ 2) (hscope he))
  · obtain ⟨i, j, hd⟩ : ∃ i j, Disjoint (cylinder (scope i) (pat i)) (cylinder (scope j) (pat j)) := by
      by_contra! hpair
      exact h (glue (fun i => (hsize i).2) hpair)
    have hsub (i : Fin 3) : cylinder (scope i) (pat i) ⊆ cov := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨i, mem_cylinder.mp hx⟩⟩
    have hle := Finset.card_le_card (Finset.union_subset (hsub i) (hsub j))
    rw [Finset.card_union_of_disjoint hd, card_cylinder (hsize i).2,
      card_cylinder (hsize j).2, (hsize i).1, (hsize j).1] at hle
    have hge : 2 * 2 ^ (n - k) ≤ cov.card := by
      unfold weight at hle
      omega
    simp [h, not_lt_of_ge hge]

end PEqualNP.Outside.L_lib_659

theorem PEqualNP.Outside.L_lib_659 :
∀ (n k : Nat), 0 < k → k ≤ n →
  ∀ (scope pat : Fin 3 → Finset (Fin n)),
    (∀ i : Fin 3, (scope i).card = k ∧ pat i ⊆ scope i) →
    Function.Injective (fun i : Fin 3 => (scope i, pat i)) →
    let u := 2^(n-k)
    let covered := ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun x => ∃ i : Fin 3, x ∩ scope i = pat i)).card
    let core := scope 0 ∩ scope 1 ∩ scope 2
    let consistent := ∃ y : Finset (Fin n), ∀ i : Fin 3, y ∩ scope i = pat i
    (covered < 2*u ↔ consistent ∧ core.card+1 = k) ∧
      (covered < 2*u → 4*covered = 7*u) := by
  intro n k _ _ scope pat hsize hinj
  exact PEqualNP.Outside.L_lib_659.solve scope pat hsize hinj
