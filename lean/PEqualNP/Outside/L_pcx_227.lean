import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_227_aux

open scoped BigOperators
open PEqualNP.ProofComplexity

def pos {n : ℕ} (hn : 0 < n) (k : ℕ) : Fin n :=
  ⟨k % n, Nat.mod_lt _ hn⟩

def fails {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (x : Fin n → Bool) (i : Fin n) : Bool :=
  !(T i (x i) (x (pos hn (i.val + 1))))

def cycCost {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (price : Fin n → ℕ)
    (x : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if fails hn T x i then price i else 0

def openCost {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (price : Fin n → ℕ)
    (h : Fin n) (x : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if i ≠ h ∧ fails hn T x i = true then price i else 0

def isArc {n : ℕ} (hn : 0 < n) (anchor : Fin n) (J : Finset (Fin n)) : Prop :=
  anchor ∉ J ∧ ∃ (s : Fin n) (k : ℕ), 0 < k ∧ k < n ∧
    J = (Finset.range k).image (fun j => pos hn (s.val + j))

def rowAxioms {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (rows : Finset (Fin n)) : Set (Clause (Fin n)) :=
  {C : Clause (Fin n) |
    ∃ i ∈ rows, ∃ a b : Bool, T i a b = false ∧
      C = {(i, !a), (pos hn (i.val + 1), !b)}}

def hasCert {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (J : Finset (Fin n)) : Prop :=
  ∃ π : List (Clause (Fin n)),
    IsRefutation (rowAxioms hn T J) π ∧ π.length ≤ 6 * J.card + 1 ∧
      ∀ C ∈ π, C.card ≤ 2

lemma resolution_sound {V : Type} [DecidableEq V] {F : Set (Clause V)} {π : List (Clause V)}
    (hder : IsDerivation F π) {a : V → Bool} (hsat : Satisfies a F) :
    ∀ C ∈ π, ClauseSat a C := by
  induction hder with
  | nil => intro C hC; cases hC
  | ax _ hC ih =>
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD'
    · exact hsat D hC
    · exact ih D hD'
  | res _ hC hD hres ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE'
    · rcases hres with ⟨v, hvC, hvD, rfl⟩
      cases hv : a v
      · rcases ih _ hC with ⟨l, hlC, hla⟩
        have hne : l ≠ (v, true) := by
          rintro rfl
          simp [hv] at hla
        exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlC⟩), hla⟩
      · rcases ih _ hD with ⟨l, hlD, hla⟩
        have hne : l ≠ (v, false) := by
          rintro rfl
          simp [hv] at hla
        exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlD⟩), hla⟩
    · exact ih E hE'

lemma refutation_hits {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    {J : Finset (Fin n)} (hcert : hasCert hn T J) (y : Fin n → Bool) :
    ∃ i ∈ J, fails hn T y i = true := by
  rcases hcert with ⟨π, ⟨hder, hempty⟩, _, _⟩
  by_contra hall
  push Not at hall
  have hsat : Satisfies y (rowAxioms hn T J) := by
    rintro C ⟨i, hiJ, a, b, hTab, rfl⟩
    have hfi : fails hn T y i ≠ true := hall i hiJ
    have hTi : T i (y i) (y (pos hn (i.val + 1))) = true := by
      unfold fails at hfi
      cases hval : T i (y i) (y (pos hn (i.val + 1))) <;> simp_all
    by_cases hya : y i = a
    · have hyb : y (pos hn (i.val + 1)) ≠ b := by
        intro heq
        rw [hya, heq, hTab] at hTi
        exact absurd hTi (by decide)
      refine ⟨(pos hn (i.val + 1), !b), by simp, ?_⟩
      cases hb : b <;> cases h : y (pos hn (i.val + 1)) <;> simp_all
    · refine ⟨(i, !a), by simp, ?_⟩
      cases ha : a <;> cases h : y i <;> simp_all
  rcases resolution_sound hder hsat ∅ hempty with ⟨l, hl, _⟩
  exact Finset.notMem_empty l hl

lemma pos_add_inj {n : ℕ} (hn : 0 < n) (s : Fin n) {j1 j2 : ℕ}
    (h1 : j1 < n) (h2 : j2 < n) (heq : pos hn (s.val + j1) = pos hn (s.val + j2)) :
    j1 = j2 := by
  have hmod : (s.val + j1) % n = (s.val + j2) % n := congrArg Fin.val heq
  have hs := s.isLt
  have hred : ∀ a : ℕ, a < n → (s.val + a) % n = if s.val + a < n then s.val + a else s.val + a - n := by
    intro a ha
    by_cases hlt : s.val + a < n
    · simp [hlt, Nat.mod_eq_of_lt hlt]
    · simp only [hlt, ↓reduceIte]
      have hsplit : s.val + a = (s.val + a - n) + n := by omega
      conv_lhs => rw [hsplit]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hred j1 h1, hred j2 h2] at hmod
  by_cases hlt1 : s.val + j1 < n <;> by_cases hlt2 : s.val + j2 < n <;>
    simp only [hlt1, hlt2, ↓reduceIte] at hmod <;> omega

lemma pos_add_succ {n : ℕ} (hn : 0 < n) (s : Fin n) (j : ℕ) :
    pos hn ((pos hn (s.val + j)).val + 1) = pos hn (s.val + (j + 1)) := by
  apply Fin.ext
  change ((s.val + j) % n + 1) % n = (s.val + (j + 1)) % n
  rw [← Nat.add_assoc, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma pos_add_pos {n : ℕ} (hn : 0 < n) (s : Fin n) (a b : ℕ) :
    pos hn ((pos hn (s.val + a)).val + b) = pos hn (s.val + (a + b)) := by
  apply Fin.ext
  change ((s.val + a) % n + b) % n = (s.val + (a + b)) % n
  rw [← Nat.add_assoc, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

def pathReach {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (s : Fin n) :
    ℕ → Bool → Prop
  | 0, _ => True
  | t + 1, b => ∃ a : Bool, pathReach hn T s t a ∧ T (pos hn (s.val + t)) a b = true

lemma exists_path_of_reach {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (s : Fin n) :
    ∀ (t : ℕ) (b : Bool), pathReach hn T s t b →
      ∃ val : ℕ → Bool, val t = b ∧
        ∀ j < t, T (pos hn (s.val + j)) (val j) (val (j + 1)) = true := by
  intro t
  induction t with
  | zero =>
    intro b _
    exact ⟨fun _ => b, rfl, fun j hj => by omega⟩
  | succ t ih =>
    intro b ⟨a, ha, hTab⟩
    obtain ⟨val, hvalt, hval⟩ := ih a ha
    refine ⟨fun j => if j = t + 1 then b else val j, by simp, ?_⟩
    intro j hj
    by_cases hjt : j = t
    · subst hjt
      have hne : j ≠ j + 1 := by omega
      simp only [hne, ↓reduceIte, hvalt]
      exact hTab
    · have hj1 : j ≠ t + 1 := by omega
      have hj2 : j + 1 ≠ t + 1 := by omega
      simp only [hj1, hj2, ↓reduceIte]
      exact hval j (by omega)

lemma not_pathReach_of_unsat {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (s : Fin n) (k : ℕ) (hk_lt : k < n)
    (hunsat : ∀ x : Fin n → Bool, ∃ j < k, T (pos hn (s.val + j)) (x (pos hn (s.val + j))) (x (pos hn (s.val + (j + 1)))) = false)
    (b : Bool) : ¬ pathReach hn T s k b := by
  classical
  intro hr
  obtain ⟨val, _, hval⟩ := exists_path_of_reach hn T s k b hr
  let x : Fin n → Bool := fun v =>
    if h : ∃ j ≤ k, pos hn (s.val + j) = v then val (Classical.choose h) else false
  have hx_eq : ∀ j ≤ k, x (pos hn (s.val + j)) = val j := by
    intro j hj
    have hex : ∃ j' ≤ k, pos hn (s.val + j') = pos hn (s.val + j) := ⟨j, hj, rfl⟩
    simp only [x, hex, ↓reduceDIte]
    have hspec := Classical.choose_spec hex
    have heq : Classical.choose hex = j :=
      pos_add_inj hn s (by omega) (by omega) hspec.2
    rw [heq]
  rcases hunsat x with ⟨j, hjk, hfalse⟩
  rw [hx_eq j (by omega), hx_eq (j + 1) (by omega), hval j hjk] at hfalse
  exact absurd hfalse (by decide)

lemma derive_step_one_bit {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (s : Fin n) (J : Finset (Fin n)) (t : ℕ) (ht_lt : t + 1 < n)
    (ht_mem : pos hn (s.val + t) ∈ J)
    (π : List (Clause (Fin n)))
    (hder : IsDerivation (rowAxioms hn T J) π)
    (hw : ∀ C ∈ π, C.card ≤ 2)
    (hinv : (∅ : Clause (Fin n)) ∈ π ∨ ∀ a : Bool, ¬ pathReach hn T s t a → {(pos hn (s.val + t), !a)} ∈ π)
    (b : Bool) (hnb : ¬ pathReach hn T s (t + 1) b) :
    ∃ π' : List (Clause (Fin n)),
      IsDerivation (rowAxioms hn T J) π' ∧
      (∀ C ∈ π', C.card ≤ 2) ∧
      π'.length ≤ π.length + 3 ∧
      (∀ C ∈ π, C ∈ π') ∧
      ((∅ : Clause (Fin n)) ∈ π' ∨ {(pos hn (s.val + (t + 1)), !b)} ∈ π') := by
  classical
  let vt := pos hn (s.val + t)
  let vt1 := pos hn (s.val + (t + 1))
  have hv_ne : vt ≠ vt1 := fun h => by
    have := pos_add_inj hn s (by omega) ht_lt h
    omega
  have hpos_succ : pos hn (vt.val + 1) = vt1 := pos_add_succ hn s t
  rcases hinv with hempty | hunits
  · exact ⟨π, hder, hw, by omega, fun _ h => h, Or.inl hempty⟩
  · have hstep_a : ∀ a : Bool, ¬ pathReach hn T s t a ∨ T vt a b = false := by
      intro a
      by_cases hr : pathReach hn T s t a
      · right
        cases hT : T vt a b
        · rfl
        · exact False.elim (hnb ⟨a, hr, hT⟩)
      · exact Or.inl hr
    have hax : ∀ a : Bool, T vt a b = false → {(vt, !a), (vt1, !b)} ∈ rowAxioms hn T J := by
      intro a hT
      exact ⟨vt, ht_mem, a, b, hT, by rw [hpos_succ]⟩
    have hcard_pair : ∀ (x y : Literal (Fin n)), ({x, y} : Clause (Fin n)).card ≤ 2 := by
      intro x y
      exact Finset.card_le_two
    have hcard_single : ∀ (x : Literal (Fin n)), ({x} : Clause (Fin n)).card ≤ 2 := by
      intro x
      simp
    rcases hstep_a false with hnf | hTf <;> rcases hstep_a true with hnt | hTt
    · have hc0 : {(vt, true)} ∈ π := by simpa [vt] using hunits false hnf
      have hc1 : {(vt, false)} ∈ π := by simpa [vt] using hunits true hnt
      have hres : IsResolvent ({(vt, true)} : Clause (Fin n)) {(vt, false)} ∅ :=
        ⟨vt, by simp, by simp, by simp⟩
      refine ⟨∅ :: π, IsDerivation.res hder hc0 hc1 hres, ?_, by simp, fun _ h => List.mem_cons_of_mem _ h, Or.inl (by simp)⟩
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC'
      · simp
      · exact hw C hC'
    · have hc0 : {(vt, true)} ∈ π := by simpa [vt] using hunits false hnf
      let ax1 : Clause (Fin n) := {(vt, false), (vt1, !b)}
      have hax1 : ax1 ∈ rowAxioms hn T J := by simpa [ax1] using hax true hTt
      let π1 := ax1 :: π
      have hder1 : IsDerivation (rowAxioms hn T J) π1 := IsDerivation.ax hder hax1
      have hne_lit : (vt1, !b) ≠ (vt, false) := fun h => hv_ne (Prod.mk.inj h).1.symm
      have hres : IsResolvent ({(vt, true)} : Clause (Fin n)) ax1 {(vt1, !b)} := by
        refine ⟨vt, by simp, by simp [ax1], ?_⟩
        ext l
        simp only [ax1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro rfl; exact Or.inr ⟨hne_lit, Or.inr rfl⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2 | h2⟩)
          · exact absurd h2 h1
          · exact absurd h2 h1
          · exact h2
      let π2 := {(vt1, !b)} :: π1
      have hder2 : IsDerivation (rowAxioms hn T J) π2 :=
        IsDerivation.res hder1 (List.mem_cons_of_mem _ hc0) (by simp [π1]) hres
      refine ⟨π2, hder2, ?_, by simp [π2, π1], fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h), Or.inr (by simp [π2, vt1])⟩
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC1
      · exact hcard_single _
      · rcases List.mem_cons.mp hC1 with rfl | hC2
        · exact hcard_pair _ _
        · exact hw C hC2
    · let ax0 : Clause (Fin n) := {(vt, true), (vt1, !b)}
      have hax0 : ax0 ∈ rowAxioms hn T J := by simpa [ax0] using hax false hTf
      have hc1 : {(vt, false)} ∈ π := by simpa [vt] using hunits true hnt
      let π1 := ax0 :: π
      have hder1 : IsDerivation (rowAxioms hn T J) π1 := IsDerivation.ax hder hax0
      have hne_lit : (vt1, !b) ≠ (vt, true) := fun h => hv_ne (Prod.mk.inj h).1.symm
      have hres : IsResolvent ax0 ({(vt, false)} : Clause (Fin n)) {(vt1, !b)} := by
        refine ⟨vt, by simp [ax0], by simp, ?_⟩
        ext l
        simp only [ax0, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro rfl; exact Or.inl ⟨hne_lit, Or.inr rfl⟩
        · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2⟩)
          · exact absurd h2 h1
          · exact h2
          · exact absurd h2 h1
      let π2 := {(vt1, !b)} :: π1
      have hder2 : IsDerivation (rowAxioms hn T J) π2 :=
        IsDerivation.res hder1 (by simp [π1]) (List.mem_cons_of_mem _ hc1) hres
      refine ⟨π2, hder2, ?_, by simp [π2, π1], fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h), Or.inr (by simp [π2, vt1])⟩
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC1
      · exact hcard_single _
      · rcases List.mem_cons.mp hC1 with rfl | hC2
        · exact hcard_pair _ _
        · exact hw C hC2
    · let ax0 : Clause (Fin n) := {(vt, true), (vt1, !b)}
      let ax1 : Clause (Fin n) := {(vt, false), (vt1, !b)}
      have hax0 : ax0 ∈ rowAxioms hn T J := by simpa [ax0] using hax false hTf
      have hax1 : ax1 ∈ rowAxioms hn T J := by simpa [ax1] using hax true hTt
      let π1 := ax0 :: π
      let π2 := ax1 :: π1
      have hder1 : IsDerivation (rowAxioms hn T J) π1 := IsDerivation.ax hder hax0
      have hder2 : IsDerivation (rowAxioms hn T J) π2 := IsDerivation.ax hder1 hax1
      have hne_t : (vt1, !b) ≠ (vt, true) := fun h => hv_ne (Prod.mk.inj h).1.symm
      have hres : IsResolvent ax0 ax1 {(vt1, !b)} := by
        refine ⟨vt, by simp [ax0], by simp [ax1], ?_⟩
        ext l
        simp only [ax0, ax1, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro rfl; exact Or.inl ⟨hne_t, Or.inr rfl⟩
        · rintro (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
          · exact absurd h2 h1
          · exact h2
          · exact absurd h2 h1
          · exact h2
      let π3 := {(vt1, !b)} :: π2
      have hder3 : IsDerivation (rowAxioms hn T J) π3 :=
        IsDerivation.res hder2 (by simp [π2, π1]) (by simp [π2]) hres
      refine ⟨π3, hder3, ?_, by simp [π3, π2, π1],
        fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)),
        Or.inr (by simp [π3, vt1])⟩
      intro C hC
      rcases List.mem_cons.mp hC with rfl | hC1
      · exact hcard_single _
      · rcases List.mem_cons.mp hC1 with rfl | hC2
        · exact hcard_pair _ _
        · rcases List.mem_cons.mp hC2 with rfl | hC3
          · exact hcard_pair _ _
          · exact hw C hC3

lemma cert_of_unsat_interval {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (s : Fin n) (k : ℕ) (_hk_pos : 0 < k) (hk_lt : k < n)
    (hunsat : ∀ x : Fin n → Bool, ∃ j < k, T (pos hn (s.val + j)) (x (pos hn (s.val + j))) (x (pos hn (s.val + (j + 1)))) = false) :
    hasCert hn T ((Finset.range k).image (fun j => pos hn (s.val + j))) := by
  let J := (Finset.range k).image (fun j => pos hn (s.val + j))
  have hJcard : J.card = k := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb heq
    exact pos_add_inj hn s (lt_trans (Finset.mem_range.mp ha) hk_lt)
      (lt_trans (Finset.mem_range.mp hb) hk_lt) heq
  have hind : ∀ t ≤ k, ∃ π : List (Clause (Fin n)),
      IsDerivation (rowAxioms hn T J) π ∧
      (∀ C ∈ π, C.card ≤ 2) ∧
      π.length ≤ 6 * t ∧
      ((∅ : Clause (Fin n)) ∈ π ∨ ∀ b : Bool, ¬ pathReach hn T s t b → {(pos hn (s.val + t), !b)} ∈ π) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨[], IsDerivation.nil, (fun _ h => by cases h), by simp, Or.inr ?_⟩
      intro b hnb
      exact False.elim (hnb trivial)
    | succ t ih =>
      intro htk
      obtain ⟨π, hder, hw, hlen, hinv⟩ := ih (by omega)
      have ht_mem : pos hn (s.val + t) ∈ J :=
        Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
      have hstepF : ∃ π1 : List (Clause (Fin n)),
          IsDerivation (rowAxioms hn T J) π1 ∧ (∀ C ∈ π1, C.card ≤ 2) ∧
          π1.length ≤ π.length + 3 ∧ (∀ C ∈ π, C ∈ π1) ∧
          ((∅ : Clause (Fin n)) ∈ π1 ∨ (¬ pathReach hn T s (t + 1) false → {(pos hn (s.val + (t + 1)), true)} ∈ π1)) := by
        by_cases hrf : pathReach hn T s (t + 1) false
        · exact ⟨π, hder, hw, by omega, fun _ h => h, Or.inr (fun h => False.elim (h hrf))⟩
        · obtain ⟨π1, hder1, hw1, hlen1, hsub1, hres1⟩ :=
            derive_step_one_bit hn T s J t (by omega) ht_mem π hder hw hinv false hrf
          refine ⟨π1, hder1, hw1, hlen1, hsub1, ?_⟩
          rcases hres1 with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (fun _ => by simpa using h2)
      rcases hstepF with ⟨π1, hder1, hw1, hlen1, hsub1, hres1⟩
      have hinv1 : (∅ : Clause (Fin n)) ∈ π1 ∨
          ∀ a : Bool, ¬ pathReach hn T s t a → {(pos hn (s.val + t), !a)} ∈ π1 := by
        rcases hinv with h1 | h2
        · exact Or.inl (hsub1 _ h1)
        · exact Or.inr (fun a ha => hsub1 _ (h2 a ha))
      have hstepT : ∃ π2 : List (Clause (Fin n)),
          IsDerivation (rowAxioms hn T J) π2 ∧ (∀ C ∈ π2, C.card ≤ 2) ∧
          π2.length ≤ π1.length + 3 ∧ (∀ C ∈ π1, C ∈ π2) ∧
          ((∅ : Clause (Fin n)) ∈ π2 ∨ (¬ pathReach hn T s (t + 1) true → {(pos hn (s.val + (t + 1)), false)} ∈ π2)) := by
        by_cases hrt : pathReach hn T s (t + 1) true
        · exact ⟨π1, hder1, hw1, by omega, fun _ h => h, Or.inr (fun h => False.elim (h hrt))⟩
        · obtain ⟨π2, hder2, hw2, hlen2, hsub2, hres2⟩ :=
            derive_step_one_bit hn T s J t (by omega) ht_mem π1 hder1 hw1 hinv1 true hrt
          refine ⟨π2, hder2, hw2, hlen2, hsub2, ?_⟩
          rcases hres2 with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (fun _ => by simpa using h2)
      rcases hstepT with ⟨π2, hder2, hw2, hlen2, hsub2, hres2⟩
      refine ⟨π2, hder2, hw2, by omega, ?_⟩
      rcases hres1 with he1 | hf1
      · exact Or.inl (hsub2 _ he1)
      · rcases hres2 with he2 | ht2
        · exact Or.inl he2
        · refine Or.inr ?_
          intro b hnb
          cases b
          · simpa using hsub2 _ (hf1 hnb)
          · simpa using ht2 hnb
  obtain ⟨π, hder, hw, hlen, hinv⟩ := hind k le_rfl
  change ∃ π', IsRefutation (rowAxioms hn T J) π' ∧ π'.length ≤ 6 * J.card + 1 ∧ ∀ C ∈ π', C.card ≤ 2
  rw [hJcard]
  rcases hinv with hempty | hunits
  · exact ⟨π, ⟨hder, hempty⟩, by omega, hw⟩
  · have hc0 : {(pos hn (s.val + k), true)} ∈ π := by
      simpa using hunits false (not_pathReach_of_unsat hn T s k hk_lt hunsat false)
    have hc1 : {(pos hn (s.val + k), false)} ∈ π := by
      simpa using hunits true (not_pathReach_of_unsat hn T s k hk_lt hunsat true)
    have hres : IsResolvent ({(pos hn (s.val + k), true)} : Clause (Fin n)) {(pos hn (s.val + k), false)} ∅ :=
      ⟨pos hn (s.val + k), by simp, by simp, by simp⟩
    refine ⟨∅ :: π, ⟨IsDerivation.res hder hc0 hc1 hres, by simp⟩, by simp; omega, ?_⟩
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC'
    · simp
    · exact hw C hC'

def Hits {m : ℕ} (D : Finset (Fin m)) (Bad : Finset (ℕ × ℕ)) : Prop :=
  ∀ I ∈ Bad, ∃ t ∈ D, I.1 ≤ t.val ∧ t.val < I.2

def MinimalHit {m : ℕ} (D : Finset (Fin m)) (Bad : Finset (ℕ × ℕ)) : Prop :=
  Hits D Bad ∧ ∀ t ∈ D, ¬ Hits (D.erase t) Bad

lemma exists_minimal_hit {m : ℕ} {Bad : Finset (ℕ × ℕ)} (D : Finset (Fin m)) (hD : Hits D Bad) :
    ∃ D' : Finset (Fin m), D' ⊆ D ∧ MinimalHit D' Bad := by
  classical
  induction hcard : D.card using Nat.strong_induction_on generalizing D with
  | ind c ih =>
    by_cases hmin : ∀ t ∈ D, ¬ Hits (D.erase t) Bad
    · exact ⟨D, Finset.Subset.refl D, hD, hmin⟩
    · push Not at hmin
      rcases hmin with ⟨t, htD, hhit'⟩
      have hlt : (D.erase t).card < c := by
        rw [Finset.card_erase_of_mem htD, hcard]
        have hpos : 0 < D.card := Finset.card_pos.mpr ⟨t, htD⟩
        omega
      obtain ⟨D', hsub', hmin'⟩ := ih (D.erase t).card hlt (D.erase t) hhit' rfl
      exact ⟨D', hsub'.trans (Finset.erase_subset t D), hmin'⟩

lemma packing_weak_duality {m : ℕ} (w : Fin m → ℕ)
    (P : Finset (ℕ × ℕ)) (qty : ℕ × ℕ → ℕ) (D : Finset (Fin m))
    (hload : ∀ t : Fin m, (∑ I ∈ P, if I.1 ≤ t.val ∧ t.val < I.2 then qty I else 0) ≤ w t)
    (hhit : Hits D P) :
    ∑ I ∈ P, qty I ≤ ∑ t ∈ D, w t := by
  have h1 : ∀ I ∈ P, qty I ≤ ∑ t ∈ D, if I.1 ≤ t.val ∧ t.val < I.2 then qty I else 0 := by
    intro I hIP
    obtain ⟨t, htD, h1', h2'⟩ := hhit I hIP
    calc qty I = (if I.1 ≤ t.val ∧ t.val < I.2 then qty I else 0) := by simp [h1', h2']
      _ ≤ ∑ s ∈ D, if I.1 ≤ s.val ∧ s.val < I.2 then qty I else 0 :=
          Finset.single_le_sum (f := fun s => if I.1 ≤ s.val ∧ s.val < I.2 then qty I else 0)
            (fun _ _ => Nat.zero_le _) htD
  calc ∑ I ∈ P, qty I
      ≤ ∑ I ∈ P, ∑ t ∈ D, if I.1 ≤ t.val ∧ t.val < I.2 then qty I else 0 :=
        Finset.sum_le_sum h1
    _ = ∑ t ∈ D, ∑ I ∈ P, if I.1 ≤ t.val ∧ t.val < I.2 then qty I else 0 :=
        Finset.sum_comm
    _ ≤ ∑ t ∈ D, w t := Finset.sum_le_sum (fun t _ => hload t)

lemma interval_packing_duality_aux {m : ℕ} :
    ∀ (k : ℕ) (a : ℕ), a + k = m →
      ∀ (Bad : Finset (ℕ × ℕ)) (w : Fin m → ℕ),
        (∀ I ∈ Bad, a ≤ I.1 ∧ I.1 < I.2 ∧ I.2 ≤ m) →
        ∃ (D : Finset (Fin m)) (P : Finset (ℕ × ℕ)) (qty : ℕ × ℕ → ℕ),
          (∀ t ∈ D, a ≤ t.val) ∧
          MinimalHit D Bad ∧
          P ⊆ Bad ∧ P.card ≤ k ∧
          (∀ I ∈ P, 0 < qty I) ∧
          (∀ t : Fin m, (∑ I ∈ P, if I.1 ≤ t.val ∧ t.val < I.2 then qty I else 0) ≤ w t) ∧
          ∑ I ∈ P, qty I = ∑ t ∈ D, w t := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro a hak Bad w hBad
    by_cases hne : Bad.Nonempty
    · obtain ⟨Istar, hIstar_mem, hIstar_min⟩ := Finset.exists_min_image Bad Prod.snd hne
      have ⟨ha_l, hl_r, hr_m⟩ := hBad Istar hIstar_mem
      let lstar := Istar.1
      let rstar := Istar.2
      let seg : Finset (Fin m) := Finset.univ.filter (fun t : Fin m => lstar ≤ t.val ∧ t.val < rstar)
      have hseg_ne : seg.Nonempty :=
        ⟨⟨lstar, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hl_r⟩⟩
      obtain ⟨tstar, htstar_seg, htstar_min⟩ := Finset.exists_min_image seg w hseg_ne
      have ⟨hl_t, ht_r⟩ := (Finset.mem_filter.mp htstar_seg).2
      let δ := w tstar
      let w' : Fin m → ℕ := fun t => if lstar ≤ t.val ∧ t.val < rstar then w t - δ else w t
      let Bad' : Finset (ℕ × ℕ) := Bad.filter (fun I => tstar.val + 1 ≤ I.1)
      have hBad' : ∀ I ∈ Bad', tstar.val + 1 ≤ I.1 ∧ I.1 < I.2 ∧ I.2 ≤ m := by
        intro I hI
        rcases Finset.mem_filter.mp hI with ⟨hIB, hlt⟩
        have ⟨_, h1, h2⟩ := hBad I hIB
        exact ⟨hlt, h1, h2⟩
      let k' := m - (tstar.val + 1)
      have hk'_lt : k' < k := by omega
      have ha'_eq : (tstar.val + 1) + k' = m := by omega
      obtain ⟨D', P', qty', hD'_ge, hD'_min, hP'_sub, hP'_card, hqty'_pos, hload', hval'⟩ :=
        ih k' hk'_lt (tstar.val + 1) ha'_eq Bad' w' hBad'
      have hIstar_not_P' : Istar ∉ P' := by
        intro hmem
        have h1 := (hBad' Istar (hP'_sub hmem)).1
        omega
      let P : Finset (ℕ × ℕ) := if δ = 0 then P' else insert Istar P'
      let qty : ℕ × ℕ → ℕ := fun I => if I = Istar then δ else qty' I
      have hP_sub : P ⊆ Bad := by
        by_cases hδ : δ = 0
        · simp only [P, hδ, ↓reduceIte]
          exact hP'_sub.trans (Finset.filter_subset _ _)
        · simp only [P, hδ, ↓reduceIte]
          intro I hI
          rcases Finset.mem_insert.mp hI with rfl | hIP'
          · exact hIstar_mem
          · exact (Finset.filter_subset _ _) (hP'_sub hIP')
      have hP_card : P.card ≤ k := by
        by_cases hδ : δ = 0
        · simp only [P, hδ, ↓reduceIte]; omega
        · simp only [P, hδ, ↓reduceIte, Finset.card_insert_of_notMem hIstar_not_P']; omega
      have hqty_pos : ∀ I ∈ P, 0 < qty I := by
        intro I hI
        by_cases hδ : δ = 0
        · simp only [P, hδ, ↓reduceIte] at hI
          have hneI : I ≠ Istar := fun h => hIstar_not_P' (h ▸ hI)
          simp only [qty, hneI, ↓reduceIte]
          exact hqty'_pos I hI
        · simp only [P, hδ, ↓reduceIte] at hI
          rcases Finset.mem_insert.mp hI with rfl | hIP'
          · simp only [qty, ↓reduceIte]; omega
          · have hneI : I ≠ Istar := fun h => hIstar_not_P' (h ▸ hIP')
            simp only [qty, hneI, ↓reduceIte]
            exact hqty'_pos I hIP'
      have hsum_P : ∑ I ∈ P, qty I = δ + ∑ I ∈ P', qty' I := by
        have hcongr : ∑ I ∈ P', qty I = ∑ I ∈ P', qty' I := by
          apply Finset.sum_congr rfl
          intro I hI
          have hneI : I ≠ Istar := fun h => hIstar_not_P' (h ▸ hI)
          simp [qty, hneI]
        by_cases hδ : δ = 0
        · simp only [P, hδ, ↓reduceIte, zero_add, hcongr]
        · simp only [P, hδ, ↓reduceIte, Finset.sum_insert hIstar_not_P', qty, hcongr]
      have hload : ∀ t : Fin m, (∑ I ∈ P, if I.1 ≤ t.val ∧ t.val < I.2 then qty I else 0) ≤ w t := by
        intro t
        have hcongr : (∑ I ∈ P', if I.1 ≤ t.val ∧ t.val < I.2 then qty I else 0) =
            ∑ I ∈ P', if I.1 ≤ t.val ∧ t.val < I.2 then qty' I else 0 := by
          apply Finset.sum_congr rfl
          intro I hI
          have hneI : I ≠ Istar := fun h => hIstar_not_P' (h ▸ hI)
          simp [qty, hneI]
        have hlt_w : ∀ s : Fin m, lstar ≤ s.val ∧ s.val < rstar → δ ≤ w s := by
          intro s hs
          exact htstar_min s (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩)
        have hload'_t := hload' t
        by_cases hδ : δ = 0
        · simp only [P, hδ, ↓reduceIte, hcongr]
          have hw'_le : w' t ≤ w t := by
            by_cases ht : lstar ≤ t.val ∧ t.val < rstar <;> simp [w', ht]
          exact hload'_t.trans hw'_le
        · simp only [P, hδ, ↓reduceIte, Finset.sum_insert hIstar_not_P', qty, hcongr]
          by_cases ht : lstar ≤ t.val ∧ t.val < rstar
          · have hδ_le : δ ≤ w t := hlt_w t ht
            simp only [lstar, rstar] at ht
            simp only [ht.1, ht.2, and_self, ↓reduceIte]
            simp only [w', lstar, rstar, ht.1, ht.2, and_self, ↓reduceIte] at hload'_t
            omega
          · simp only [lstar, rstar] at ht
            simp only [ht, ↓reduceIte, zero_add]
            simp only [w', lstar, rstar, ht, ↓reduceIte] at hload'_t
            exact hload'_t
      let D'_in := D'.filter (fun t : Fin m => t.val < rstar)
      have hD'_in_card : D'_in.card ≤ 1 := by
        by_contra hgt1
        have h2 : 1 < D'_in.card := by omega
        obtain ⟨t1, ht1, t2, ht2, ht12⟩ := Finset.one_lt_card.mp h2
        have ht1D' : t1 ∈ D' := (Finset.mem_filter.mp ht1).1
        have ht2D' : t2 ∈ D' := (Finset.mem_filter.mp ht2).1
        have ht1_lt : t1.val < rstar := (Finset.mem_filter.mp ht1).2
        have ht2_lt : t2.val < rstar := (Finset.mem_filter.mp ht2).2
        have hval_ne : t1.val ≠ t2.val := fun h => ht12 (Fin.ext h)
        have hred : ∀ u v : Fin m, u ∈ D' → v ∈ D' → u.val < v.val → v.val < rstar → False := by
          intro u v hu hv huv hvr
          apply hD'_min.2 u hu
          intro I hIB'
          obtain ⟨s, hsD', hs1, hs2⟩ := hD'_min.1 I hIB'
          by_cases hsu : s = u
          · rw [hsu] at hs1 hs2
            have hr_ge : rstar ≤ I.2 := hIstar_min I ((Finset.filter_subset _ _) hIB')
            have hvne : v ≠ u := fun h => by rw [h] at huv; omega
            exact ⟨v, Finset.mem_erase.mpr ⟨hvne, hv⟩, by omega, by omega⟩
          · exact ⟨s, Finset.mem_erase.mpr ⟨hsu, hsD'⟩, hs1, hs2⟩
        rcases lt_or_gt_of_ne hval_ne with hlt | hgt
        · exact hred t1 t2 ht1D' ht2D' hlt ht2_lt
        · exact hred t2 t1 ht2D' ht1D' hgt ht1_lt
      have hD0 : ∃ D0 : Finset (Fin m),
          (∀ t ∈ D0, a ≤ t.val) ∧ Hits D0 Bad ∧ ∑ t ∈ D0, w t = δ + ∑ t ∈ D', w' t := by
        by_cases hne_in : D'_in.Nonempty
        · have hcard1 : D'_in.card = 1 := by
            have hpos := Finset.card_pos.mpr hne_in
            omega
          obtain ⟨t1, ht1_eq⟩ := Finset.card_eq_one.mp hcard1
          have ht1_mem : t1 ∈ D'_in := by rw [ht1_eq]; exact Finset.mem_singleton_self t1
          have ht1D' : t1 ∈ D' := (Finset.mem_filter.mp ht1_mem).1
          have ht1_lt : t1.val < rstar := (Finset.mem_filter.mp ht1_mem).2
          have ht1_ge : tstar.val + 1 ≤ t1.val := hD'_ge t1 ht1D'
          refine ⟨D', fun t ht => by have := hD'_ge t ht; omega, ?_, ?_⟩
          · intro I hIB
            by_cases hI' : tstar.val + 1 ≤ I.1
            · exact hD'_min.1 I (Finset.mem_filter.mpr ⟨hIB, hI'⟩)
            · have hr_ge : rstar ≤ I.2 := hIstar_min I hIB
              exact ⟨t1, ht1D', by omega, by omega⟩
          · rw [← Finset.add_sum_erase D' w ht1D', ← Finset.add_sum_erase D' w' ht1D']
            have hwt1 : w t1 = δ + w' t1 := by
              have hlt1 : lstar ≤ t1.val ∧ t1.val < rstar := ⟨by omega, ht1_lt⟩
              have hδ_le : δ ≤ w t1 := htstar_min t1 (Finset.mem_filter.mpr ⟨Finset.mem_univ t1, hlt1⟩)
              simp only [w', hlt1.1, hlt1.2, and_self, ↓reduceIte]
              omega
            have hrest : ∑ t ∈ D'.erase t1, w t = ∑ t ∈ D'.erase t1, w' t := by
              apply Finset.sum_congr rfl
              intro t ht
              rcases Finset.mem_erase.mp ht with ⟨hne_t1, htD'⟩
              have ht_ge : ¬ t.val < rstar := by
                intro hlt
                have hmem : t ∈ D'_in := Finset.mem_filter.mpr ⟨htD', hlt⟩
                rw [ht1_eq, Finset.mem_singleton] at hmem
                exact hne_t1 hmem
              simp [w', ht_ge]
            rw [hwt1, hrest]
            omega
        · rw [Finset.not_nonempty_iff_eq_empty] at hne_in
          have htstar_not_D' : tstar ∉ D' := fun h => by
            have := hD'_ge tstar h
            omega
          refine ⟨insert tstar D', ?_, ?_, ?_⟩
          · intro t ht
            rcases Finset.mem_insert.mp ht with rfl | htD'
            · omega
            · have := hD'_ge t htD'; omega
          · intro I hIB
            by_cases hI' : tstar.val + 1 ≤ I.1
            · obtain ⟨t, htD', h1, h2⟩ := hD'_min.1 I (Finset.mem_filter.mpr ⟨hIB, hI'⟩)
              exact ⟨t, Finset.mem_insert_of_mem htD', h1, h2⟩
            · have hr_ge : rstar ≤ I.2 := hIstar_min I hIB
              exact ⟨tstar, Finset.mem_insert_self _ _, by omega, by omega⟩
          · rw [Finset.sum_insert htstar_not_D']
            congr 1
            apply Finset.sum_congr rfl
            intro t htD'
            have ht_ge : ¬ t.val < rstar := by
              intro hlt
              have hmem : t ∈ D'_in := Finset.mem_filter.mpr ⟨htD', hlt⟩
              rw [hne_in] at hmem
              exact Finset.notMem_empty t hmem
            simp [w', ht_ge]
      obtain ⟨D0, hD0_ge, hD0_hit, hD0_sum⟩ := hD0
      obtain ⟨D, hD_sub, hD_min⟩ := exists_minimal_hit D0 hD0_hit
      have hD_le : ∑ t ∈ D, w t ≤ ∑ I ∈ P, qty I := by
        calc ∑ t ∈ D, w t ≤ ∑ t ∈ D0, w t := Finset.sum_le_sum_of_subset hD_sub
          _ = δ + ∑ t ∈ D', w' t := hD0_sum
          _ = δ + ∑ I ∈ P', qty' I := by rw [hval']
          _ = ∑ I ∈ P, qty I := hsum_P.symm
      have hD_ge_val : ∑ I ∈ P, qty I ≤ ∑ t ∈ D, w t :=
        packing_weak_duality w P qty D hload (fun I hIP => hD_min.1 I (hP_sub hIP))
      exact ⟨D, P, qty, fun t ht => hD0_ge t (hD_sub ht), hD_min, hP_sub, hP_card, hqty_pos,
        hload, le_antisymm hD_ge_val hD_le⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      refine ⟨∅, ∅, fun _ => 0, (fun _ h => by cases h),
        ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩,
        Finset.empty_subset _, by simp, (fun _ h => by cases h), (fun _ => by simp), by simp⟩

lemma exists_witness_of_hit {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool)
    (h : Fin n) (D : Finset (Fin (n - 1)))
    (hhit : ∀ (l r : ℕ), l < r → r ≤ n - 1 →
      (∀ x : Fin n → Bool, ∃ j < r - l,
        T (pos hn ((pos hn (h.val + 1 + l)).val + j))
          (x (pos hn ((pos hn (h.val + 1 + l)).val + j)))
          (x (pos hn ((pos hn (h.val + 1 + l)).val + (j + 1)))) = false) →
      ∃ t ∈ D, l ≤ t.val ∧ t.val < r) :
    ∃ x : Fin n → Bool, ∀ t : Fin (n - 1), t ∉ D → fails hn T x (pos hn (h.val + 1 + t.val)) = false := by
  classical
  let m := n - 1
  let v : ℕ → Fin n := fun k => pos hn (h.val + 1 + k)
  have hv_inj : ∀ a b : ℕ, a ≤ m → b ≤ m → v a = v b → a = b := by
    intro a b ha hb heq
    have hs : pos hn (h.val + 1 + a) = pos hn ((pos hn (h.val + 1)).val + a) := by
      simpa [Nat.add_assoc] using (pos_add_pos hn h 1 a).symm
    have hs' : pos hn (h.val + 1 + b) = pos hn ((pos hn (h.val + 1)).val + b) := by
      simpa [Nat.add_assoc] using (pos_add_pos hn h 1 b).symm
    have h1 : pos hn ((pos hn (h.val + 1)).val + a) = pos hn ((pos hn (h.val + 1)).val + b) := by
      rw [← hs, ← hs']; exact heq
    exact pos_add_inj hn (pos hn (h.val + 1)) (by omega) (by omega) h1
  let runStart : ℕ → ℕ := fun k =>
    let S := (D.filter (fun d => d.val < k)).image (fun d => d.val + 1)
    if hne : S.Nonempty then S.max' hne else 0
  let runEnd : ℕ → ℕ := fun k =>
    let S := (D.filter (fun d => k ≤ d.val)).image (fun d => d.val)
    if hne : S.Nonempty then S.min' hne else m
  have hrunStart_le : ∀ k, runStart k ≤ k := by
    intro k
    dsimp only [runStart]
    split_ifs with hne
    · rw [Finset.max'_le_iff]
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨d, hd, rfl⟩
      have := (Finset.mem_filter.mp hd).2
      omega
    · exact Nat.zero_le k
  have hrunEnd_ge : ∀ k ≤ m, k ≤ runEnd k ∧ runEnd k ≤ m := by
    intro k hk
    dsimp only [runEnd]
    split_ifs with hne
    · constructor
      · rw [Finset.le_min'_iff]
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨d, hd, rfl⟩
        exact (Finset.mem_filter.mp hd).2
      · have hmem := Finset.min'_mem _ hne
        rcases Finset.mem_image.mp hmem with ⟨d, _, hd_eq⟩
        have := d.isLt
        omega
    · exact ⟨hk, le_rfl⟩
  have hrun_no_D : ∀ k ≤ m, ∀ d ∈ D, ¬ (runStart k ≤ d.val ∧ d.val < runEnd k) := by
    intro k hk d hdD ⟨h1, h2⟩
    by_cases hdk : d.val < k
    · have hmem : d.val + 1 ∈ (D.filter (fun d => d.val < k)).image (fun d => d.val + 1) :=
        Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hdD, hdk⟩, rfl⟩
      have hne : ((D.filter (fun d => d.val < k)).image (fun d => d.val + 1)).Nonempty := ⟨_, hmem⟩
      have hle := Finset.le_max' _ _ hmem
      simp only [runStart, hne, ↓reduceDIte] at h1
      omega
    · have hkd : k ≤ d.val := by omega
      have hmem : d.val ∈ (D.filter (fun d => k ≤ d.val)).image (fun d => d.val) :=
        Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hdD, hkd⟩, rfl⟩
      have hne : ((D.filter (fun d => k ≤ d.val)).image (fun d => d.val)).Nonempty := ⟨_, hmem⟩
      have hge := Finset.min'_le _ _ hmem
      simp only [runEnd, hne, ↓reduceDIte] at h2
      omega
  have hrunStart_step : ∀ t : Fin m, t ∉ D → runStart (t.val + 1) = runStart t.val := by
    intro t htD
    have hflt : D.filter (fun d => d.val < t.val + 1) = D.filter (fun d => d.val < t.val) := by
      ext d
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro hdD
      have hne : d.val ≠ t.val := fun h => htD (Fin.ext h ▸ hdD)
      omega
    simp only [runStart, hflt]
  have hrunEnd_step : ∀ t : Fin m, t ∉ D → runEnd (t.val + 1) = runEnd t.val := by
    intro t htD
    have hflt : D.filter (fun d => t.val + 1 ≤ d.val) = D.filter (fun d => t.val ≤ d.val) := by
      ext d
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro hdD
      have hne : d.val ≠ t.val := fun h => htD (Fin.ext h ▸ hdD)
      omega
    simp only [runEnd, hflt]
  have hsat_run : ∀ l r : ℕ, l < r → r ≤ m → (∀ d ∈ D, ¬ (l ≤ d.val ∧ d.val < r)) →
      ∃ y : Fin n → Bool, ∀ j < r - l,
        T (pos hn ((v l).val + j)) (y (pos hn ((v l).val + j))) (y (pos hn ((v l).val + (j + 1)))) = true := by
    intro l r hlr hrm hnoD
    by_contra hunsat
    push Not at hunsat
    have hunsat' : ∀ y : Fin n → Bool, ∃ j < r - l,
        T (pos hn ((v l).val + j)) (y (pos hn ((v l).val + j))) (y (pos hn ((v l).val + (j + 1)))) = false := by
      intro y
      rcases hunsat y with ⟨j, hj, hne⟩
      exact ⟨j, hj, Bool.eq_false_iff.mpr hne⟩
    obtain ⟨d, hdD, h1, h2⟩ := hhit l r hlr hrm hunsat'
    exact hnoD d hdD ⟨h1, h2⟩
  let pickY : ℕ → ℕ → (Fin n → Bool) := fun l r =>
    if hcond : l < r ∧ r ≤ m ∧ (∀ d ∈ D, ¬ (l ≤ d.val ∧ d.val < r)) then
      Classical.choose (hsat_run l r hcond.1 hcond.2.1 hcond.2.2)
    else fun _ => false
  have hpickY_spec : ∀ l r : ℕ, l < r → r ≤ m → (∀ d ∈ D, ¬ (l ≤ d.val ∧ d.val < r)) →
      ∀ j < r - l,
        T (pos hn ((v l).val + j)) (pickY l r (pos hn ((v l).val + j)))
          (pickY l r (pos hn ((v l).val + (j + 1)))) = true := by
    intro l r hlr hrm hnoD
    have hcond : l < r ∧ r ≤ m ∧ (∀ d ∈ D, ¬ (l ≤ d.val ∧ d.val < r)) := ⟨hlr, hrm, hnoD⟩
    have hpy : pickY l r = Classical.choose (hsat_run l r hlr hrm hnoD) := by
      dsimp only [pickY]
      exact dif_pos hcond
    rw [hpy]
    exact Classical.choose_spec (hsat_run l r hlr hrm hnoD)
  let x : Fin n → Bool := fun w =>
    if hex : ∃ k ≤ m, v k = w then
      let k := Classical.choose hex
      pickY (runStart k) (runEnd k) w
    else false
  have hx_at : ∀ k ≤ m, x (v k) = pickY (runStart k) (runEnd k) (v k) := by
    intro k hk
    have hex : ∃ k' ≤ m, v k' = v k := ⟨k, hk, rfl⟩
    simp only [x, hex, ↓reduceDIte]
    have hspec := Classical.choose_spec hex
    have heq : Classical.choose hex = k := hv_inj _ _ hspec.1 hk hspec.2
    rw [heq]
  refine ⟨x, ?_⟩
  intro t htD
  have hts : runStart t.val ≤ t.val := hrunStart_le t.val
  have hte1 : t.val + 1 ≤ runEnd (t.val + 1) ∧ runEnd (t.val + 1) ≤ m :=
    hrunEnd_ge (t.val + 1) (by have := t.isLt; omega)
  have hte : t.val + 1 ≤ runEnd t.val ∧ runEnd t.val ≤ m := by
    rwa [hrunEnd_step t htD] at hte1
  have hlt_sr : runStart t.val < runEnd t.val := by omega
  have hnoD : ∀ d ∈ D, ¬ (runStart t.val ≤ d.val ∧ d.val < runEnd t.val) :=
    hrun_no_D t.val (by have := t.isLt; omega)
  let j := t.val - runStart t.val
  have hj_lt : j < runEnd t.val - runStart t.val := by omega
  have hspec := hpickY_spec (runStart t.val) (runEnd t.val) hlt_sr hte.2 hnoD j hj_lt
  have hv_j : pos hn ((v (runStart t.val)).val + j) = v t.val := by
    have h1 := pos_add_pos hn h (1 + runStart t.val) j
    have h2 : 1 + runStart t.val + j = 1 + t.val := by omega
    simpa [v, Nat.add_assoc, h2] using h1
  have hv_j1 : pos hn ((v (runStart t.val)).val + (j + 1)) = v (t.val + 1) := by
    have h1 := pos_add_pos hn h (1 + runStart t.val) (j + 1)
    have h2 : 1 + runStart t.val + (j + 1) = 1 + (t.val + 1) := by omega
    simpa [v, Nat.add_assoc, h2] using h1
  rw [hv_j, hv_j1] at hspec
  have hpos_next : pos hn ((v t.val).val + 1) = v (t.val + 1) := by
    have h1 := pos_add_pos hn h (1 + t.val) 1
    simpa [v, Nat.add_assoc] using h1
  have hx1 : x (v t.val) = pickY (runStart t.val) (runEnd t.val) (v t.val) :=
    hx_at t.val (by have := t.isLt; omega)
  have hx2 : x (v (t.val + 1)) = pickY (runStart t.val) (runEnd t.val) (v (t.val + 1)) := by
    rw [hx_at (t.val + 1) (by have := t.isLt; omega), hrunStart_step t htD, hrunEnd_step t htD]
  unfold fails
  change (!(T (v t.val) (x (v t.val)) (x (pos hn ((v t.val).val + 1))))) = false
  rw [hpos_next, hx1, hx2, hspec]
  rfl

lemma solve_cut {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (price : Fin n → ℕ)
    (h : Fin n) :
    ∃ (pack : Finset (Finset (Fin n))) (qty : Finset (Fin n) → ℕ) (witness : Fin n → Bool),
      let value := ∑ J ∈ pack, qty J
      pack.card < n ∧
      (∀ J ∈ pack, isArc hn h J ∧ hasCert hn T J ∧ 0 < qty J) ∧
      (∀ i : Fin n, (∑ J ∈ pack, if i ∈ J then qty J else 0) ≤ price i) ∧
      openCost hn T price h witness = value ∧
      ∀ y : Fin n → Bool, value ≤ openCost hn T price h y := by
  classical
  let m := n - 1
  let row : Fin m → Fin n := fun t => pos hn (h.val + 1 + t.val)
  have hrow_ne_h : ∀ t : Fin m, row t ≠ h := by
    intro t heq
    have h1 : pos hn (h.val + 0) = h := by
      apply Fin.ext
      change (h.val + 0) % n = h.val
      rw [add_zero, Nat.mod_eq_of_lt h.isLt]
    have h2 : pos hn (h.val + (1 + t.val)) = pos hn (h.val + 0) := by
      simpa [row, Nat.add_assoc] using heq.trans h1.symm
    have := pos_add_inj hn h (by have := t.isLt; omega) hn h2
    omega
  have hrow_inj : Function.Injective row := by
    intro t1 t2 heq
    have h1 : pos hn (h.val + (1 + t1.val)) = pos hn (h.val + (1 + t2.val)) := by
      simpa [row, Nat.add_assoc] using heq
    have h2 := pos_add_inj hn h (by have := t1.isLt; omega) (by have := t2.isLt; omega) h1
    exact Fin.ext (by omega)
  have hrow_surj : ∀ i : Fin n, i ≠ h → ∃ t : Fin m, row t = i := by
    intro i hih
    let d := (i.val + n - (h.val + 1)) % n
    have hd_lt_n : d < n := Nat.mod_lt _ hn
    have hpos_d : pos hn (h.val + 1 + d) = i := by
      apply Fin.ext
      change (h.val + 1 + (i.val + n - (h.val + 1)) % n) % n = i.val
      have hi := i.isLt
      have hh := h.isLt
      by_cases hle : h.val + 1 ≤ i.val
      · have hsub : i.val + n - (h.val + 1) = (i.val - (h.val + 1)) + n := by omega
        have hlt_s : i.val - (h.val + 1) < n := by omega
        rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hlt_s]
        have heq : h.val + 1 + (i.val - (h.val + 1)) = i.val := by omega
        rw [heq, Nat.mod_eq_of_lt hi]
      · have hlt_s : i.val + n - (h.val + 1) < n := by omega
        rw [Nat.mod_eq_of_lt hlt_s]
        have heq : h.val + 1 + (i.val + n - (h.val + 1)) = i.val + n := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    have hd_lt_m : d < m := by
      by_contra hge
      have hdeq : d = n - 1 := by omega
      have h1 : pos hn (h.val + 1 + (n - 1)) = h := by
        apply Fin.ext
        change (h.val + 1 + (n - 1)) % n = h.val
        have heq : h.val + 1 + (n - 1) = h.val + n := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt h.isLt]
      rw [hdeq, h1] at hpos_d
      exact hih hpos_d.symm
    exact ⟨⟨d, hd_lt_m⟩, hpos_d⟩
  let ivToFinset : ℕ × ℕ → Finset (Fin n) := fun I =>
    (Finset.range (I.2 - I.1)).image (fun j => pos hn ((pos hn (h.val + 1 + I.1)).val + j))
  have hiv_mem_iff : ∀ (I : ℕ × ℕ) (t : Fin m), I.1 < I.2 → I.2 ≤ m →
      (row t ∈ ivToFinset I ↔ I.1 ≤ t.val ∧ t.val < I.2) := by
    intro I t h12 h2m
    simp only [ivToFinset, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, heq⟩
      have hpos1 : pos hn ((pos hn (h.val + 1 + I.1)).val + j) = pos hn (h.val + (1 + (I.1 + j))) := by
        have hp := pos_add_pos hn h (1 + I.1) j
        simpa [Nat.add_assoc] using hp
      have hpos2 : row t = pos hn (h.val + (1 + t.val)) := by simp [row, Nat.add_assoc]
      rw [hpos1, hpos2] at heq
      have hinj := pos_add_inj hn h (by omega) (by have := t.isLt; omega) heq
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨t.val - I.1, by omega, ?_⟩
      have hp := pos_add_pos hn h (1 + I.1) (t.val - I.1)
      have heq : 1 + I.1 + (t.val - I.1) = 1 + t.val := by omega
      simpa [row, Nat.add_assoc, heq] using hp
  have hiv_not_h : ∀ I : ℕ × ℕ, I.1 < I.2 → I.2 ≤ m → h ∉ ivToFinset I := by
    intro I h12 h2m hmem
    rcases Finset.mem_image.mp hmem with ⟨j, hj, heq⟩
    have hj_lt := Finset.mem_range.mp hj
    have hpos1 : pos hn ((pos hn (h.val + 1 + I.1)).val + j) = row ⟨I.1 + j, by omega⟩ := by
      have hp := pos_add_pos hn h (1 + I.1) j
      simpa [row, Nat.add_assoc] using hp
    rw [hpos1] at heq
    exact hrow_ne_h ⟨I.1 + j, by omega⟩ heq
  have hiv_inj : ∀ I1 I2 : ℕ × ℕ, I1.1 < I1.2 → I1.2 ≤ m → I2.1 < I2.2 → I2.2 ≤ m →
      ivToFinset I1 = ivToFinset I2 → I1 = I2 := by
    intro I1 I2 h1a h1b h2a h2b heq
    have hiff : ∀ t : Fin m, (I1.1 ≤ t.val ∧ t.val < I1.2) ↔ (I2.1 ≤ t.val ∧ t.val < I2.2) := by
      intro t
      rw [← hiv_mem_iff I1 t h1a h1b, ← hiv_mem_iff I2 t h2a h2b, heq]
    have h1_le : I2.1 ≤ I1.1 := ((hiff ⟨I1.1, by omega⟩).mp ⟨le_rfl, h1a⟩).1
    have h2_le : I1.1 ≤ I2.1 := ((hiff ⟨I2.1, by omega⟩).mpr ⟨le_rfl, h2a⟩).1
    have h1_ge : I1.2 - 1 < I2.2 := ((hiff ⟨I1.2 - 1, by omega⟩).mp ⟨by dsimp; omega, by dsimp; omega⟩).2
    have h2_ge : I2.2 - 1 < I1.2 := ((hiff ⟨I2.2 - 1, by omega⟩).mpr ⟨by dsimp; omega, by dsimp; omega⟩).2
    exact Prod.ext (by omega) (by omega)
  let Bad : Finset (ℕ × ℕ) :=
    ((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter (fun I =>
      I.1 < I.2 ∧ I.2 ≤ m ∧
      ∀ x : Fin n → Bool, ∃ j < I.2 - I.1,
        T (pos hn ((pos hn (h.val + 1 + I.1)).val + j))
          (x (pos hn ((pos hn (h.val + 1 + I.1)).val + j)))
          (x (pos hn ((pos hn (h.val + 1 + I.1)).val + (j + 1)))) = false)
  let w : Fin m → ℕ := fun t => price (row t)
  have hBad_bounds : ∀ I ∈ Bad, 0 ≤ I.1 ∧ I.1 < I.2 ∧ I.2 ≤ m := by
    intro I hI
    have h := (Finset.mem_filter.mp hI).2
    exact ⟨Nat.zero_le _, h.1, h.2.1⟩
  obtain ⟨D, P, qtyI, _, hD_min, hP_sub, hP_card, hqtyI_pos, hloadI, hvalI⟩ :=
    interval_packing_duality_aux m 0 (zero_add m) Bad w hBad_bounds
  have hP_inj : Set.InjOn ivToFinset (P : Set (ℕ × ℕ)) := by
    intro I1 h1 I2 h2 heq
    have hb1 := hBad_bounds I1 (hP_sub h1)
    have hb2 := hBad_bounds I2 (hP_sub h2)
    exact hiv_inj I1 I2 hb1.2.1 hb1.2.2 hb2.2.1 hb2.2.2 heq
  let pack : Finset (Finset (Fin n)) := P.image ivToFinset
  let qty : Finset (Fin n) → ℕ := fun J =>
    if hex : ∃ I ∈ P, ivToFinset I = J then qtyI (Classical.choose hex) else 0
  have hqty_eq : ∀ I ∈ P, qty (ivToFinset I) = qtyI I := by
    intro I hIP
    have hex : ∃ I' ∈ P, ivToFinset I' = ivToFinset I := ⟨I, hIP, rfl⟩
    simp only [qty, hex, ↓reduceDIte]
    have hspec := Classical.choose_spec hex
    rw [hP_inj hspec.1 hIP hspec.2]
  have hvalue_eq : ∑ J ∈ pack, qty J = ∑ I ∈ P, qtyI I := by
    rw [Finset.sum_image hP_inj]
    exact Finset.sum_congr rfl (fun I hI => hqty_eq I hI)
  have hpack_card : pack.card < n := by
    have h1 : pack.card = P.card := Finset.card_image_of_injOn hP_inj
    omega
  have hpack_props : ∀ J ∈ pack, isArc hn h J ∧ hasCert hn T J ∧ 0 < qty J := by
    intro J hJ
    rcases Finset.mem_image.mp hJ with ⟨I, hIP, rfl⟩
    have hIB := (Finset.mem_filter.mp (hP_sub hIP)).2
    have h12 : I.1 < I.2 := hIB.1
    have h2m : I.2 ≤ m := hIB.2.1
    refine ⟨⟨hiv_not_h I h12 h2m, pos hn (h.val + 1 + I.1), I.2 - I.1, by omega, by omega, rfl⟩,
      cert_of_unsat_interval hn T (pos hn (h.val + 1 + I.1)) (I.2 - I.1) (by omega) (by omega) hIB.2.2,
      by rw [hqty_eq I hIP]; exact hqtyI_pos I hIP⟩
  have hpack_load : ∀ i : Fin n, (∑ J ∈ pack, if i ∈ J then qty J else 0) ≤ price i := by
    intro i
    by_cases hih : i = h
    · rw [hih]
      have hzero : ∑ J ∈ pack, (if h ∈ J then qty J else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro J hJ
        have hnot := (hpack_props J hJ).1.1
        simp [hnot]
      rw [hzero]
      exact Nat.zero_le _
    · obtain ⟨t, rfl⟩ := hrow_surj i hih
      rw [Finset.sum_image hP_inj]
      have hcongr : ∑ I ∈ P, (if row t ∈ ivToFinset I then qty (ivToFinset I) else 0) =
          ∑ I ∈ P, if I.1 ≤ t.val ∧ t.val < I.2 then qtyI I else 0 := by
        apply Finset.sum_congr rfl
        intro I hIP
        have hb := hBad_bounds I (hP_sub hIP)
        simp only [hiv_mem_iff I t hb.2.1 hb.2.2, hqty_eq I hIP]
      rw [hcongr]
      exact hloadI t
  have hdual_lb : ∀ y : Fin n → Bool, (∑ J ∈ pack, qty J) ≤ openCost hn T price h y := by
    intro y
    have hhit_y : ∀ J ∈ pack, qty J ≤ ∑ i : Fin n, if i ≠ h ∧ fails hn T y i = true ∧ i ∈ J then qty J else 0 := by
      intro J hJ
      have ⟨harc, hcert, _⟩ := hpack_props J hJ
      obtain ⟨i, hiJ, hfi⟩ := refutation_hits hn T hcert y
      have hih : i ≠ h := fun heq => harc.1 (heq ▸ hiJ)
      calc qty J = (if i ≠ h ∧ fails hn T y i = true ∧ i ∈ J then qty J else 0) := by
            simp [hih, hfi, hiJ]
        _ ≤ ∑ k : Fin n, if k ≠ h ∧ fails hn T y k = true ∧ k ∈ J then qty J else 0 :=
            Finset.single_le_sum (f := fun k => if k ≠ h ∧ fails hn T y k = true ∧ k ∈ J then qty J else 0)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    calc ∑ J ∈ pack, qty J
        ≤ ∑ J ∈ pack, ∑ i : Fin n, if i ≠ h ∧ fails hn T y i = true ∧ i ∈ J then qty J else 0 :=
          Finset.sum_le_sum hhit_y
      _ = ∑ i : Fin n, ∑ J ∈ pack, if i ≠ h ∧ fails hn T y i = true ∧ i ∈ J then qty J else 0 :=
          Finset.sum_comm
      _ ≤ ∑ i : Fin n, if i ≠ h ∧ fails hn T y i = true then price i else 0 := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hcond : i ≠ h ∧ fails hn T y i = true
          · simp [hcond.1, hcond.2]
            exact hpack_load i
          · simp only [hcond, ↓reduceIte]
            have h0 : ∑ J ∈ pack, (if i ≠ h ∧ fails hn T y i = true ∧ i ∈ J then qty J else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro J _
              have hnot : ¬ (i ≠ h ∧ fails hn T y i = true ∧ i ∈ J) := fun hc => hcond ⟨hc.1, hc.2.1⟩
              simp [hnot]
            rw [h0]
  have hD_hits_all : ∀ (l r : ℕ), l < r → r ≤ m →
      (∀ x : Fin n → Bool, ∃ j < r - l,
        T (pos hn ((pos hn (h.val + 1 + l)).val + j))
          (x (pos hn ((pos hn (h.val + 1 + l)).val + j)))
          (x (pos hn ((pos hn (h.val + 1 + l)).val + (j + 1)))) = false) →
      ∃ t ∈ D, l ≤ t.val ∧ t.val < r := by
    intro l r hlr hrm hunsat
    have hmem : (l, r) ∈ Bad := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩, hlr, hrm, hunsat⟩
    exact hD_min.1 (l, r) hmem
  obtain ⟨witness, hwit⟩ := exists_witness_of_hit hn T h D hD_hits_all
  have hwit_le : openCost hn T price h witness ≤ ∑ J ∈ pack, qty J := by
    have hopen_eq : openCost hn T price h witness =
        ∑ t : Fin m, if fails hn T witness (row t) = true then w t else 0 := by
      unfold openCost
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ h)]
      simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add]
      have himg : Finset.univ.erase h = Finset.univ.image row := by
        ext i
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
        constructor
        · exact hrow_surj i
        · rintro ⟨t, rfl⟩; exact hrow_ne_h t
      rw [himg, Finset.sum_image (fun a _ b _ h => hrow_inj h)]
      apply Finset.sum_congr rfl
      intro t _
      simp [hrow_ne_h t, w]
    rw [hopen_eq, hvalue_eq, hvalI]
    calc ∑ t : Fin m, (if fails hn T witness (row t) = true then w t else 0)
        ≤ ∑ t : Fin m, (if t ∈ D then w t else 0) := by
          apply Finset.sum_le_sum
          intro t _
          by_cases htD : t ∈ D
          · by_cases hf : fails hn T witness (row t) = true <;> simp [htD, hf]
          · simp [htD, row, hwit t htD]
      _ = ∑ t ∈ D, w t := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hwit_eq : openCost hn T price h witness = ∑ J ∈ pack, qty J :=
    le_antisymm hwit_le (hdual_lb witness)
  exact ⟨pack, qty, witness, hpack_card, hpack_props, hpack_load, hwit_eq, hdual_lb⟩

lemma cost_eq_add_openCost {n : ℕ} (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (price : Fin n → ℕ)
    (h : Fin n) (y : Fin n → Bool) :
    cycCost hn T price y = (if fails hn T y h = true then price h else 0) + openCost hn T price h y := by
  unfold cycCost openCost
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ h)]
  conv_rhs => rw [← Finset.add_sum_erase Finset.univ (fun i => if i ≠ h ∧ fails hn T y i = true then price i else 0) (Finset.mem_univ h)]
  simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hih : i ≠ h := (Finset.mem_erase.mp hi).1
  simp [hih]

lemma main_proof (n : ℕ) (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (price : Fin n → ℕ) :
    ∃ (pack : Fin n → Finset (Finset (Fin n))) (qty : Fin n → Finset (Fin n) → ℕ)
      (witness : Fin n → (Fin n → Bool)),
      let value := fun cut : Fin n => ∑ J ∈ pack cut, qty cut J
      (∀ h : Fin n, (pack h).card < n ∧
        (∀ J ∈ pack h, isArc hn h J ∧ hasCert hn T J ∧ 0 < qty h J) ∧
        (∀ i : Fin n, (∑ J ∈ pack h, if i ∈ J then qty h J else 0) ≤ price i) ∧
        openCost hn T price h (witness h) = value h ∧ ∀ y : Fin n → Bool, value h ≤ openCost hn T price h y) ∧
      ((∀ z : Fin n → Bool, ∃ i : Fin n, fails hn T z i = true) →
        ∃ (x : Fin n → Bool) (h : Fin n), cycCost hn T price x = price h + value h ∧
          (∀ k : Fin n, cycCost hn T price x ≤ price k + value k) ∧
          ∀ y : Fin n → Bool, cycCost hn T price x ≤ cycCost hn T price y) := by
  classical
  let pack : Fin n → Finset (Finset (Fin n)) := fun h =>
    Classical.choose (solve_cut hn T price h)
  let qty : Fin n → Finset (Fin n) → ℕ := fun h =>
    Classical.choose (Classical.choose_spec (solve_cut hn T price h))
  let witness : Fin n → (Fin n → Bool) := fun h =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (solve_cut hn T price h)))
  have hspec : ∀ h : Fin n,
      (pack h).card < n ∧
      (∀ J ∈ pack h, isArc hn h J ∧ hasCert hn T J ∧ 0 < qty h J) ∧
      (∀ i : Fin n, (∑ J ∈ pack h, if i ∈ J then qty h J else 0) ≤ price i) ∧
      openCost hn T price h (witness h) = ∑ J ∈ pack h, qty h J ∧
      ∀ y : Fin n → Bool, (∑ J ∈ pack h, qty h J) ≤ openCost hn T price h y := fun h =>
    Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (solve_cut hn T price h)))
  refine ⟨pack, qty, witness, hspec, ?_⟩
  intro hunsat_all
  let value : Fin n → ℕ := fun cut => ∑ J ∈ pack cut, qty cut J
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨h, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun k : Fin n => price k + value k) hne
  have hlb_any : ∀ y : Fin n → Bool, price h + value h ≤ cycCost hn T price y := by
    intro y
    obtain ⟨k, hfk⟩ := hunsat_all y
    have h1 : price h + value h ≤ price k + value k := hmin k (Finset.mem_univ k)
    have h2 : value k ≤ openCost hn T price k y := (hspec k).2.2.2.2 y
    have h3 : cycCost hn T price y = price k + openCost hn T price k y := by
      have hc := cost_eq_add_openCost hn T price k y
      simp only [hfk, ↓reduceIte] at hc
      exact hc
    omega
  let x := witness h
  have hcost_x_le : cycCost hn T price x ≤ price h + value h := by
    have hc := cost_eq_add_openCost hn T price h x
    have ho : openCost hn T price h x = value h := (hspec h).2.2.2.1
    rw [ho] at hc
    by_cases hf : fails hn T x h = true <;> simp only [hf, Bool.false_eq_true, ↓reduceIte] at hc <;> omega
  have hcost_x_eq : cycCost hn T price x = price h + value h :=
    le_antisymm hcost_x_le (hlb_any x)
  refine ⟨x, h, hcost_x_eq, ?_, ?_⟩
  · intro k
    rw [hcost_x_eq]
    exact hmin k (Finset.mem_univ k)
  · intro y
    rw [hcost_x_eq]
    exact hlb_any y

end PEqualNP.Outside.L_pcx_227_aux

theorem PEqualNP.Outside.L_pcx_227 :
∀ (n : ℕ) (hn : 0 < n) (T : Fin n → Bool → Bool → Bool) (price : Fin n → ℕ),
  let pos := fun k : ℕ => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let fails := fun (x : Fin n → Bool) (i : Fin n) => !(T i (x i) (x (pos (i.val + 1))))
  let cost := fun assignment => ∑ i : Fin n, if fails assignment i then price i else 0
  let openCost := fun (h : Fin n) (word : Fin n → Bool) =>
    ∑ i : Fin n, if i ≠ h ∧ fails word i = true then price i else 0
  let arc := fun (anchor : Fin n) (J : Finset (Fin n)) =>
    anchor ∉ J ∧ ∃ (s : Fin n) (k : ℕ), 0 < k ∧ k < n ∧
      J = (Finset.range k).image (fun j => pos (s.val + j))
  let axioms := fun (rows : Finset (Fin n)) =>
    {C : PEqualNP.ProofComplexity.Clause (Fin n) |
      ∃ i ∈ rows, ∃ a b : Bool, T i a b = false ∧
        C = {(i, !a), (pos (i.val + 1), !b)}}
  let cert := fun (J : Finset (Fin n)) =>
    ∃ π : List (PEqualNP.ProofComplexity.Clause (Fin n)),
      PEqualNP.ProofComplexity.IsRefutation (axioms J) π ∧ π.length ≤ 6 * J.card + 1 ∧
        ∀ C ∈ π, C.card ≤ 2
  ∃ (pack : Fin n → Finset (Finset (Fin n))) (qty : Fin n → Finset (Fin n) → ℕ)
    (witness : Fin n → (Fin n → Bool)),
    let value := fun cut : Fin n => ∑ J ∈ pack cut, qty cut J
    (∀ h : Fin n, (pack h).card < n ∧
      (∀ J ∈ pack h, arc h J ∧ cert J ∧ 0 < qty h J) ∧
      (∀ i : Fin n, (∑ J ∈ pack h, if i ∈ J then qty h J else 0) ≤ price i) ∧
      openCost h (witness h) = value h ∧ ∀ y : Fin n → Bool, value h ≤ openCost h y) ∧
    ((∀ z : Fin n → Bool, ∃ i : Fin n, fails z i = true) →
      ∃ (x : Fin n → Bool) (h : Fin n), cost x = price h + value h ∧
        (∀ k : Fin n, cost x ≤ price k + value k) ∧ ∀ y : Fin n → Bool, cost x ≤ cost y) := by
  intro n hn T price
  dsimp only
  exact PEqualNP.Outside.L_pcx_227_aux.main_proof n hn T price
