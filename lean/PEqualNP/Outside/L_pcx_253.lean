import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_253_aux

private def walkP {n : ℕ} (E : Fin n → Fin n → Bool → Prop) (m : ℕ)
    (v : ℕ → Fin n) (s : ℕ → Bool) : Prop :=
  ∀ i < m, E (v i) (v (i + 1)) (s i)

private def parityB (m : ℕ) (s : ℕ → Bool) : Bool :=
  decide (Odd (((Finset.range m).filter (fun i => s i = true)).card))

private theorem parityB_zero (s : ℕ → Bool) : parityB 0 s = false := by
  simp [parityB]

private theorem parityB_one (s : ℕ → Bool) : parityB 1 s = s 0 := by
  unfold parityB
  rw [Finset.range_one]
  cases hs : s 0 <;> simp [Finset.filter_singleton, hs]

private theorem decide_odd_add (a b : ℕ) :
    decide (Odd (a + b)) = (decide (Odd a) ^^ decide (Odd b)) := by
  by_cases ha : Odd a <;> by_cases hb : Odd b <;>
    simp [ha, hb, Nat.odd_add, ← Nat.not_odd_iff_even]

private theorem parityB_congr (m : ℕ) (s1 s2 : ℕ → Bool) (h : ∀ i < m, s1 i = s2 i) :
    parityB m s1 = parityB m s2 := by
  have hfil : (Finset.range m).filter (fun i => s1 i = true) =
      (Finset.range m).filter (fun i => s2 i = true) := by
    refine Finset.filter_congr ?_
    intro i hi
    rw [h i (Finset.mem_range.mp hi)]
  unfold parityB
  rw [hfil]

private def catS (m1 : ℕ) (s1 s2 : ℕ → Bool) (i : ℕ) : Bool :=
  if i < m1 then s1 i else s2 (i - m1)

private def catV {n : ℕ} (m1 : ℕ) (v1 v2 : ℕ → Fin n) (i : ℕ) : Fin n :=
  if i ≤ m1 then v1 i else v2 (i - m1)

private def revS (m : ℕ) (s : ℕ → Bool) (i : ℕ) : Bool :=
  s (m - 1 - i)

private def revV {n : ℕ} (m : ℕ) (v : ℕ → Fin n) (i : ℕ) : Fin n :=
  v (m - i)

private theorem parityB_cat (m1 m2 : ℕ) (s1 s2 : ℕ → Bool) :
    parityB (m1 + m2) (catS m1 s1 s2) = (parityB m1 s1 ^^ parityB m2 s2) := by
  unfold parityB
  rw [← decide_odd_add]
  congr 2
  let S1 := (Finset.range m1).filter (fun i => s1 i = true)
  let S2 := ((Finset.range m2).filter (fun i => s2 i = true)).image (· + m1)
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [S1, S2, Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hx1 hx2
    rcases hx2 with ⟨y, _, rfl⟩
    omega
  have hunion : (Finset.range (m1 + m2)).filter (fun i => catS m1 s1 s2 i = true) = S1 ∪ S2 := by
    ext x
    simp only [S1, S2, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    dsimp only [catS]
    split_ifs with hx
    · constructor
      · rintro ⟨_, hs⟩
        exact Or.inl ⟨hx, hs⟩
      · rintro (⟨_, hs⟩ | ⟨y, _, hy⟩)
        · exact ⟨by omega, hs⟩
        · omega
    · constructor
      · rintro ⟨hlt, hs⟩
        right
        exact ⟨x - m1, ⟨by omega, hs⟩, by omega⟩
      · rintro (⟨hlt, _⟩ | ⟨y, ⟨hy, hs⟩, rfl⟩)
        · omega
        · refine ⟨by omega, ?_⟩
          simpa [Nat.add_sub_cancel] using hs
  have hcard2 : S2.card = ((Finset.range m2).filter (fun i => s2 i = true)).card :=
    Finset.card_image_of_injective _ (fun a b h => by omega)
  rw [hunion, Finset.card_union_of_disjoint hdisj, hcard2]

private theorem parityB_split (m mid : ℕ) (hmid : mid ≤ m) (s : ℕ → Bool) :
    parityB m s = (parityB mid s ^^ parityB (m - mid) (fun i => s (mid + i))) := by
  have heq : m = mid + (m - mid) := by omega
  have h1 := parityB_cat mid (m - mid) s (fun i => s (mid + i))
  rw [← heq] at h1
  rw [← h1]
  refine parityB_congr m s _ ?_
  intro i hi
  unfold catS
  by_cases h : i < mid
  · simp [h]
  · simp only [h, ↓reduceIte]
    congr 1
    omega

private theorem parityB_rev (m : ℕ) (s : ℕ → Bool) :
    parityB m (revS m s) = parityB m s := by
  have hcard : ((Finset.range m).filter (fun i => revS m s i = true)).card =
      ((Finset.range m).filter (fun i => s i = true)).card := by
    refine Finset.card_bij' (fun i _ => m - 1 - i) (fun i _ => m - 1 - i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact ⟨by omega, hi.2⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
      refine ⟨by omega, ?_⟩
      dsimp only [revS]
      have heq : m - 1 - (m - 1 - i) = i := by omega
      rw [heq]
      exact hi.2
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      omega
  unfold parityB
  rw [hcard]

private theorem walkP_cat {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    {m1 m2 : ℕ} {v1 v2 : ℕ → Fin n} {s1 s2 : ℕ → Bool}
    (h1 : walkP E m1 v1 s1) (h2 : walkP E m2 v2 s2) (hmid : v1 m1 = v2 0) :
    walkP E (m1 + m2) (catV m1 v1 v2) (catS m1 s1 s2) := by
  intro i hi
  unfold catV catS
  by_cases hlt : i < m1
  · have hle1 : i ≤ m1 := by omega
    have hle2 : i + 1 ≤ m1 := by omega
    simp only [hlt, hle1, hle2, ↓reduceIte]
    exact h1 i hlt
  · by_cases heq : i = m1
    · subst heq
      have hgt : ¬ (i + 1 ≤ i) := by omega
      simp only [hlt, le_refl, hgt, ↓reduceIte, Nat.add_sub_cancel_left, Nat.sub_self, hmid]
      exact h2 0 (by omega)
    · have hgt1 : ¬ (i ≤ m1) := by omega
      have hgt2 : ¬ (i + 1 ≤ m1) := by omega
      simp only [hlt, hgt1, hgt2, ↓reduceIte]
      have hsub : i + 1 - m1 = i - m1 + 1 := by omega
      rw [hsub]
      exact h2 (i - m1) (by omega)

private theorem walkP_rev {n : ℕ} {E : Fin n → Fin n → Bool → Prop}
    (hsym : ∀ u v b, E u v b → E v u b)
    {m : ℕ} {v : ℕ → Fin n} {s : ℕ → Bool} (hw : walkP E m v s) :
    walkP E m (revV m v) (revS m s) := by
  intro i hi
  unfold revV revS
  have hlt : m - 1 - i < m := by omega
  have h1 := hw (m - 1 - i) hlt
  have heq1 : m - 1 - i + 1 = m - i := by omega
  have heq2 : m - (i + 1) = m - 1 - i := by omega
  rw [heq1] at h1
  rw [heq2]
  exact hsym _ _ _ h1

private def HasStrategy {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (d : ℕ) (S : Finset (Fin n)) (z : Fin n → Bool) : Prop :=
  ∃ ask : List Bool → Fin n,
    ∀ (x : Fin n → Bool) (ans : Fin d → Bool), (∀ i ∈ S, x i = z i) →
      let queried := fun i : Fin d => ask ((List.ofFn ans).take i.val)
      (∀ i, ans i = x (queried i)) →
      let seen := S ∪ Finset.univ.image queried
      ∃ u ∈ seen, ∃ v ∈ seen, ∃ b : Bool, E u v b ∧ x v ≠ (x u ^^ b)

private def Witness {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (d : ℕ) (S : Finset (Fin n)) (z : Fin n → Bool) : Prop :=
  (∃ (m : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool), 1 ≤ m ∧ m ≤ 2 ^ d ∧
    walkP E m v s ∧ v 0 ∈ S ∧ v m ∈ S ∧ z (v m) ≠ (z (v 0) ^^ parityB m s)) ∨
  (0 < d ∧ ∃ (m : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool), 1 ≤ m ∧
    2 * m ≤ 2 ^ d ∧ walkP E m v s ∧ v 0 = v m ∧ parityB m s = true)

private theorem hasStrategy_zero_iff {n : ℕ} (hn : 0 < n) (E : Fin n → Fin n → Bool → Prop)
    (S : Finset (Fin n)) (z : Fin n → Bool) :
    HasStrategy E 0 S z ↔ ∃ u ∈ S, ∃ v ∈ S, ∃ b : Bool, E u v b ∧ z v ≠ (z u ^^ b) := by
  constructor
  · rintro ⟨ask, hask⟩
    obtain ⟨u, hu, v, hv, b, hE, hne⟩ :=
      hask z Fin.elim0 (fun _ _ => rfl) (fun i => Fin.elim0 i)
    simp only [Finset.univ_eq_empty, Finset.image_empty, Finset.union_empty] at hu hv
    exact ⟨u, hu, v, hv, b, hE, hne⟩
  · rintro ⟨u, hu, v, hv, b, hE, hne⟩
    refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
    intro x ans hx queried _ seen
    refine ⟨u, Finset.mem_union_left _ hu, v, Finset.mem_union_left _ hv, b, hE, ?_⟩
    rw [hx u hu, hx v hv]
    exact hne

private theorem witness_zero_iff {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (S : Finset (Fin n)) (z : Fin n → Bool) :
    Witness E 0 S z ↔ ∃ u ∈ S, ∃ v ∈ S, ∃ b : Bool, E u v b ∧ z v ≠ (z u ^^ b) := by
  constructor
  · rintro (⟨m, v, s, hm1, hm2, hw, hv0, hvm, hne⟩ | ⟨h0, _⟩)
    · have hm : m = 1 := by simp at hm2; omega
      subst hm
      rw [parityB_one] at hne
      exact ⟨v 0, hv0, v 1, hvm, s 0, hw 0 (by omega), hne⟩
    · omega
  · rintro ⟨u, hu, v, hv, b, hE, hne⟩
    left
    refine ⟨1, fun i => if i = 0 then u else v, fun _ => b, le_refl 1, by simp, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using hE
    · simpa using hu
    · simpa using hv
    · simpa [parityB_one] using hne

private theorem hasStrategy_succ_iff {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (d : ℕ) (S : Finset (Fin n)) (z : Fin n → Bool) :
    HasStrategy E (d + 1) S z ↔
      ∃ q : Fin n, ∀ a : Bool, (q ∈ S → a = z q) →
        HasStrategy E d (insert q S) (Function.update z q a) := by
  constructor
  · rintro ⟨ask, hask⟩
    refine ⟨ask [], ?_⟩
    intro a ha
    refine ⟨fun l => ask (a :: l), ?_⟩
    intro x ans' hx' queried' hans' seen'
    have hxS : ∀ i ∈ S, x i = z i := by
      intro i hi
      have h1 := hx' i (Finset.mem_insert_of_mem hi)
      by_cases hiq : i = ask []
      · subst hiq
        rw [Function.update_self] at h1
        rw [h1, ha hi]
      · rwa [Function.update_of_ne hiq] at h1
    have hxq : x (ask []) = a := by
      have h1 := hx' (ask []) (Finset.mem_insert_self _ _)
      rwa [Function.update_self] at h1
    let ans : Fin (d + 1) → Bool := Fin.cons a ans'
    have hans : ∀ i : Fin (d + 1), ans i = x (ask ((List.ofFn ans).take i.val)) := by
      intro i
      refine Fin.cases ?_ ?_ i
      · simp [ans, hxq]
      · intro j
        have htake : (List.ofFn ans).take j.succ.val = a :: (List.ofFn ans').take j.val := by
          simp [ans, List.ofFn_succ, List.take_succ_cons]
        rw [htake]
        simpa [ans, queried'] using hans' j
    obtain ⟨u, hu, v, hv, b, hE, hne⟩ := hask x ans hxS hans
    have hseen : S ∪ Finset.univ.image (fun i : Fin (d + 1) => ask ((List.ofFn ans).take i.val)) =
        seen' := by
      ext w
      simp only [seen', queried', Finset.mem_union, Finset.mem_insert, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro (hw | ⟨i, rfl⟩)
        · exact Or.inl (Or.inr hw)
        · refine Fin.cases ?_ ?_ i
          · exact Or.inl (Or.inl (by simp))
          · intro j
            right
            refine ⟨j, ?_⟩
            have htake : (List.ofFn ans).take j.succ.val = a :: (List.ofFn ans').take j.val := by
              simp [ans, List.ofFn_succ, List.take_succ_cons]
            rw [htake]
      · rintro ((rfl | hw) | ⟨j, rfl⟩)
        · exact Or.inr ⟨0, by simp⟩
        · exact Or.inl hw
        · right
          refine ⟨j.succ, ?_⟩
          have htake : (List.ofFn ans).take j.succ.val = a :: (List.ofFn ans').take j.val := by
            simp [ans, List.ofFn_succ, List.take_succ_cons]
          rw [htake]
    rw [hseen] at hu hv
    exact ⟨u, hu, v, hv, b, hE, hne⟩
  · rintro ⟨q, hq⟩
    classical
    let askB : Bool → List Bool → Fin n := fun a =>
      if h : (q ∈ S → a = z q) then Classical.choose (hq a h) else fun _ => q
    let ask : List Bool → Fin n := fun l =>
      match l with
      | [] => q
      | a :: rest => askB a rest
    refine ⟨ask, ?_⟩
    intro x ans hxS queried hans seen
    have h0 : ans 0 = x q := by
      have := hans 0
      simpa [queried, ask] using this
    have hvalid : q ∈ S → ans 0 = z q := by
      intro hqS
      rw [h0, hxS q hqS]
    have hspec := Classical.choose_spec (hq (ans 0) hvalid)
    have hx' : ∀ i ∈ insert q S, x i = Function.update z q (ans 0) i := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hiS
      · rw [Function.update_self, h0]
      · by_cases hiq : i = q
        · subst hiq; rw [Function.update_self, h0]
        · rw [Function.update_of_ne hiq]; exact hxS i hiS
    let ans' : Fin d → Bool := Fin.tail ans
    have haskB : askB (ans 0) = Classical.choose (hq (ans 0) hvalid) := by
      dsimp only [askB]
      split_ifs
      rfl
    have htake_fn : ∀ j : Fin d,
        (List.ofFn ans).take j.succ.val = ans 0 :: (List.ofFn ans').take j.val := by
      intro j
      simp only [ans', List.ofFn_succ]
      rfl
    have hans' : ∀ i : Fin d,
        ans' i = x (Classical.choose (hq (ans 0) hvalid) ((List.ofFn ans').take i.val)) := by
      intro i
      have hi := hans i.succ
      simp only [queried] at hi
      rw [htake_fn i] at hi
      simpa [ans', Fin.tail, ask, haskB] using hi
    obtain ⟨u, hu, v, hv, b, hE, hne⟩ := hspec x ans' hx' hans'
    have hseen : insert q S ∪
        Finset.univ.image (fun i : Fin d =>
          Classical.choose (hq (ans 0) hvalid) ((List.ofFn ans').take i.val)) =
        seen := by
      ext w
      simp only [seen, queried, Finset.mem_union, Finset.mem_insert, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro ((rfl | hw) | ⟨j, rfl⟩)
        · exact Or.inr ⟨0, by simp [ask]⟩
        · exact Or.inl hw
        · right
          refine ⟨j.succ, ?_⟩
          rw [htake_fn j]
          simp [ask, haskB]
      · rintro (hw | ⟨i, rfl⟩)
        · exact Or.inl (Or.inr hw)
        · refine Fin.cases ?_ ?_ i
          · exact Or.inl (Or.inl (by simp [ask]))
          · intro j
            right
            refine ⟨j, ?_⟩
            rw [htake_fn j]
            simp [ask, haskB]
    rw [hseen] at hu hv
    exact ⟨u, hu, v, hv, b, hE, hne⟩

private theorem witness_succ_iff {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (hsym : ∀ u v b, E u v b → E v u b)
    (d : ℕ) (S : Finset (Fin n)) (z : Fin n → Bool) :
    Witness E (d + 1) S z ↔
      ∃ q : Fin n, ∀ a : Bool, (q ∈ S → a = z q) →
        Witness E d (insert q S) (Function.update z q a) := by
  constructor
  · rintro (⟨m, v, s, hm1, hm2, hw, hv0, hvm, hne⟩ | ⟨_, m, v, s, hm1, hm2, hw, hloop, hodd⟩)
    · by_cases hle : m ≤ 2 ^ d
      · refine ⟨v 0, ?_⟩
        intro a ha
        left
        have hupd : ∀ i ∈ S, Function.update z (v 0) a i = z i := by
          intro i hi
          by_cases h : i = v 0
          · subst h; rw [Function.update_self, ha hv0]
          · rw [Function.update_of_ne h]
        refine ⟨m, v, s, hm1, hle, hw, Finset.mem_insert_of_mem hv0,
          Finset.mem_insert_of_mem hvm, ?_⟩
        rw [hupd (v m) hvm, hupd (v 0) hv0]
        exact hne
      · let mid := m / 2
        have hmid1 : 1 ≤ mid := by
          have : 1 ≤ 2 ^ d := Nat.one_le_two_pow
          omega
        have hmid_le : mid ≤ 2 ^ d := by
          rw [Nat.pow_succ] at hm2
          omega
        have hrem1 : 1 ≤ m - mid := by omega
        have hrem_le : m - mid ≤ 2 ^ d := by
          rw [Nat.pow_succ] at hm2
          omega
        refine ⟨v mid, ?_⟩
        intro a ha
        let z' := Function.update z (v mid) a
        have hz'S : ∀ i ∈ S, z' i = z i := by
          intro i hi
          by_cases h : i = v mid
          · subst h; simp [z', ha hi]
          · simp [z', h]
        have hz'mid : z' (v mid) = a := by simp [z']
        have hps := parityB_split m mid (by omega) s
        by_cases hleft : a ≠ (z (v 0) ^^ parityB mid s)
        · left
          refine ⟨mid, v, s, hmid1, hmid_le, fun i hi => hw i (by omega),
            Finset.mem_insert_of_mem hv0, Finset.mem_insert_self _ _, ?_⟩
          change z' (v mid) ≠ (z' (v 0) ^^ parityB mid s)
          rw [hz'mid, hz'S (v 0) hv0]
          exact hleft
        · left
          have ha_eq : a = (z (v 0) ^^ parityB mid s) := by
            by_contra h
            exact hleft h
          refine ⟨m - mid, fun i => v (mid + i), fun i => s (mid + i), hrem1, hrem_le,
            fun i hi => by
              dsimp only
              have h1 := hw (mid + i) (by omega)
              have h2 : mid + (i + 1) = mid + i + 1 := by omega
              rw [h2]; exact h1,
            by simp,
            by
              dsimp only
              have heq : mid + (m - mid) = m := by omega
              rw [heq]; exact Finset.mem_insert_of_mem hvm, ?_⟩
          change z' (v (mid + (m - mid))) ≠ (z' (v (mid + 0)) ^^ parityB (m - mid) (fun i => s (mid + i)))
          have heq : mid + (m - mid) = m := by omega
          rw [heq, Nat.add_zero, hz'S (v m) hvm, hz'mid, ha_eq]
          intro hcontra
          apply hne
          rw [hps, hcontra]
          cases z (v 0) <;> cases parityB mid s <;> cases parityB (m - mid) (fun i => s (mid + i)) <;> rfl
    · refine ⟨v 0, ?_⟩
      intro a _
      left
      have hm_le : m ≤ 2 ^ d := by
        rw [Nat.pow_succ] at hm2
        omega
      refine ⟨m, v, s, hm1, hm_le, hw, Finset.mem_insert_self _ _,
        by rw [← hloop]; exact Finset.mem_insert_self _ _, ?_⟩
      rw [← hloop, Function.update_self, hodd]
      cases a <;> decide
  · intro hex
    by_contra hno
    obtain ⟨q, hq⟩ := hex
    let Forced : Bool → Prop := fun b =>
      ∃ (m : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool), m ≤ 2 ^ d ∧
        walkP E m v s ∧ v 0 ∈ S ∧ v m = q ∧ b = (z (v 0) ^^ parityB m s)
    have hnot_both : ¬ (Forced false ∧ Forced true) := by
      rintro ⟨⟨m1, v1, s1, hm1, hw1, hv10, hv1m, hb1⟩, ⟨m2, v2, s2, hm2, hw2, hv20, hv2m, hb2⟩⟩
      apply hno
      left
      have hpos : 1 ≤ m1 + m2 := by
        by_contra h0
        have hm10 : m1 = 0 := by omega
        have hm20 : m2 = 0 := by omega
        subst hm10 hm20
        rw [parityB_zero] at hb1 hb2
        rw [hv1m] at hb1
        rw [hv2m] at hb2
        simp at hb1 hb2
        rw [hb1] at hb2
        exact Bool.false_ne_true hb2
      have hle : m1 + m2 ≤ 2 ^ (d + 1) := by
        rw [Nat.pow_succ]
        omega
      have hmid : v1 m1 = revV m2 v2 0 := by
        simp [revV, hv1m, hv2m]
      refine ⟨m1 + m2, catV m1 v1 (revV m2 v2), catS m1 s1 (revS m2 s2), hpos, hle,
        walkP_cat hw1 (walkP_rev hsym hw2) hmid, ?_, ?_, ?_⟩
      · simp [catV, hv10]
      · by_cases hm20 : m2 = 0
        · subst hm20
          simp [catV, hv1m, ← hv2m, hv20]
        · have hgt : ¬ (m1 + m2 ≤ m1) := by omega
          simp [catV, hgt, revV, hv20]
      · have hv0' : catV m1 v1 (revV m2 v2) 0 = v1 0 := by simp [catV]
        have hvm' : catV m1 v1 (revV m2 v2) (m1 + m2) = v2 0 := by
          by_cases hm20 : m2 = 0
          · subst hm20; simp [catV, hv1m, ← hv2m]
          · have hgt : ¬ (m1 + m2 ≤ m1) := by omega
            simp [catV, hgt, revV]
        rw [hv0', hvm', parityB_cat, parityB_rev]
        intro heq
        have h1 : (z (v1 0) ^^ parityB m1 s1) = false := hb1.symm
        have h2 : (z (v2 0) ^^ parityB m2 s2) = true := hb2.symm
        revert h1 h2 heq
        generalize z (v1 0) = A
        generalize z (v2 0) = B
        generalize parityB m1 s1 = P1
        generalize parityB m2 s2 = P2
        revert A B P1 P2
        decide
    classical
    let a : Bool := if Forced true then true else false
    have hforced_eq : ∀ b : Bool, Forced b → a = b := by
      intro b hb
      cases b
      · have hnt : ¬ Forced true := fun ht => hnot_both ⟨hb, ht⟩
        simp [a, hnt]
      · simp [a, hb]
    have ha_valid : q ∈ S → a = z q := by
      intro hqS
      apply hforced_eq (z q)
      refine ⟨0, fun _ => q, fun _ => false, Nat.zero_le _, fun i hi => by omega, hqS, rfl, ?_⟩
      simp [parityB_zero]
    have hz'S : ∀ i ∈ S, Function.update z q a i = z i := by
      intro i hi
      by_cases h : i = q
      · subst h; rw [Function.update_self, ha_valid hi]
      · rw [Function.update_of_ne h]
    rcases hq a ha_valid with ⟨m, v, s, hm1, hm2, hw, hv0, hvm, hne⟩ | ⟨hd0, m, v, s, hm1, hm2, hw, hloop, hodd⟩
    · rcases Finset.mem_insert.mp hv0 with hv0q | hv0S <;>
        rcases Finset.mem_insert.mp hvm with hvmq | hvmS
      · apply hno
        right
        refine ⟨Nat.succ_pos d, m, v, s, hm1, by rw [Nat.pow_succ]; omega, hw,
          hv0q.trans hvmq.symm, ?_⟩
        rw [hv0q, hvmq, Function.update_self] at hne
        cases hp : parityB m s
        · rw [hp] at hne; simp at hne
        · rfl
      · have hrev_forced : Forced (z (v m) ^^ parityB m s) := by
          refine ⟨m, revV m v, revS m s, hm2, walkP_rev hsym hw, ?_, ?_, ?_⟩
          · simp [revV, hvmS]
          · simp [revV, hv0q]
          · rw [parityB_rev]; simp [revV]
        have haeq := hforced_eq _ hrev_forced
        rw [hv0q, Function.update_self, hz'S (v m) hvmS] at hne
        apply hne
        rw [haeq]
        cases z (v m) <;> cases parityB m s <;> rfl
      · have hfor : Forced (z (v 0) ^^ parityB m s) :=
          ⟨m, v, s, hm2, hw, hv0S, hvmq, rfl⟩
        have haeq := hforced_eq _ hfor
        rw [hvmq, Function.update_self, hz'S (v 0) hv0S] at hne
        exact hne haeq
      · apply hno
        left
        rw [hz'S (v m) hvmS, hz'S (v 0) hv0S] at hne
        refine ⟨m, v, s, hm1, hm2.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d)),
          hw, hv0S, hvmS, hne⟩
    · apply hno
      right
      exact ⟨Nat.succ_pos d, m, v, s, hm1,
        hm2.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ d)), hw, hloop, hodd⟩

theorem main_aux (n : ℕ) (hn : 0 < n) (E : Fin n → Fin n → Bool → Prop)
    (hsym : ∀ u v b, E u v b → E v u b)
    (S : Finset (Fin n)) (z : Fin n → Bool) (d : ℕ) :
    HasStrategy E d S z ↔ Witness E d S z := by
  induction d generalizing S z with
  | zero =>
    rw [hasStrategy_zero_iff hn, witness_zero_iff]
  | succ d ih =>
    rw [hasStrategy_succ_iff, witness_succ_iff E hsym]
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, fun a ha => (ih (insert q S) (Function.update z q a)).mp (hq a ha)⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, fun a ha => (ih (insert q S) (Function.update z q a)).mpr (hq a ha)⟩

end PEqualNP.Outside.L_pcx_253_aux

theorem PEqualNP.Outside.L_pcx_253 :
∀ (n : ℕ), 0 < n → ∀ E : Fin n → Fin n → Bool → Prop,
  (∀ u v b, E u v b → E v u b) → (∀ u b, ¬ E u u b) →
  ∀ (S : Finset (Fin n)) (z : Fin n → Bool) (d : ℕ),
    let walk := fun (m : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool) =>
      ∀ i < m, E (v i) (v (i+1)) (s i)
    let parity := fun (m : ℕ) (s : ℕ → Bool) =>
      decide (Odd (((Finset.range m).filter (fun i => s i = true)).card))
    (∃ ask : List Bool → Fin n,
      ∀ (x : Fin n → Bool) (ans : Fin d → Bool), (∀ i ∈ S, x i = z i) →
        let queried := fun i : Fin d => ask ((List.ofFn ans).take i.val)
        (∀ i, ans i = x (queried i)) →
        let seen := S ∪ Finset.univ.image queried
        ∃ u ∈ seen, ∃ v ∈ seen, ∃ b : Bool, E u v b ∧ x v ≠ (x u ^^ b)) ↔
    (∃ (m : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool), 1 ≤ m ∧ m ≤ 2^d ∧
      walk m v s ∧ v 0 ∈ S ∧ v m ∈ S ∧ z (v m) ≠ (z (v 0) ^^ parity m s)) ∨
    (0 < d ∧ ∃ (m : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool), 1 ≤ m ∧
      2*m ≤ 2^d ∧ walk m v s ∧ v 0 = v m ∧ parity m s = true) := by
  intro n hn E hsym _ S z d walk parity
  exact PEqualNP.Outside.L_pcx_253_aux.main_aux n hn E hsym S z d
