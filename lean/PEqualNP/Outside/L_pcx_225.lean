import PEqualNP.Defs

/-!
# L-pcx-225: space-bounded resolution refutations of cyclic window CNFs

Let `m = min w n`. Stage `i` remembers `K i`: the variables below `i` that are opening
variables (below `w`) or among the last `w` ones. Every clause of `F` lives at its greatest
variable `j`, inside `insert j (K j)` (a wrapped window has its low part in the opening).

The `Dead`/`dead_step`/`one_state` machinery is adapted from L-pcx-206 (scan to resolution).
Here the work is scheduled for clause space: the stages below `m` are a depth-first search
holding one sibling clause per pending pivot, and for each full opening the stages from `n`
down to `m` are a backward dynamic program that holds two layers of at most `2 ^ w` clauses.
Each memory state costs at most two downloaded clauses of F and one resolvent.
-/

namespace PEqualNP.Outside.L_pcx_225

open PEqualNP.ProofComplexity

variable {n : ℕ}

/-- Every literal of `D` is on a variable of `S` and is falsified by `a`. -/
def Good (S : Finset (Fin n)) (a : Fin n → Bool) (D : Clause (Fin n)) : Prop :=
  ∀ l ∈ D, l.1 ∈ S ∧ a l.1 ≠ l.2

/-- The memory state at stage `i` is dead. -/
def Dead (F : Set (Clause (Fin n))) (K : ℕ → Finset (Fin n)) (i : ℕ) (a : Fin n → Bool) :
    Prop :=
  ∀ a' : Fin n → Bool, (∀ v ∈ K i, a' v = a v) →
    ∃ j : Fin n, i ≤ j.val ∧ ∃ C ∈ F, (∀ l ∈ C, l.1 ∈ insert j (K j.val)) ∧ ¬ ClauseSat a' C

theorem good_card {S : Finset (Fin n)} {a : Fin n → Bool} {D : Clause (Fin n)}
    (h : Good S a D) : D.card ≤ S.card := by
  apply Finset.card_le_card_of_injOn (fun l => l.1)
  · intro l hl
    exact (h l hl).1
  · intro l hl l' hl' he
    have h1 := (h l hl).2
    have h2 := (h l' hl').2
    simp only at he
    have : l.2 = l'.2 := by
      rw [he] at h1
      cases hx : a l'.1 <;> cases hy : l.2 <;> cases hz : l'.2 <;> simp_all
    exact Prod.ext he this

theorem not_sat_iff {a : Fin n → Bool} {C : Clause (Fin n)} :
    ¬ ClauseSat a C ↔ ∀ l ∈ C, a l.1 ≠ l.2 := by
  unfold ClauseSat
  push_neg
  rfl

theorem sat_congr {a a' : Fin n → Bool} {C : Clause (Fin n)}
    (h : ∀ l ∈ C, a l.1 = a' l.1) : ClauseSat a C ↔ ClauseSat a' C := by
  unfold ClauseSat
  constructor
  · rintro ⟨l, hl, he⟩
    exact ⟨l, hl, (h l hl) ▸ he⟩
  · rintro ⟨l, hl, he⟩
    exact ⟨l, hl, (h l hl).symm ▸ he⟩

section scan

variable (K : ℕ → Finset (Fin n))

theorem keep_lt (h0 : K 0 = ∅) (hs : ∀ i (hi : i < n), K (i + 1) ⊆ insert ⟨i, hi⟩ (K i)) :
    ∀ i, i ≤ n → ∀ v ∈ K i, v.val < i := by
  intro i
  induction i with
  | zero => intro _ v hv; simp [h0] at hv
  | succ i ih =>
    intro hi v hv
    have := hs i (by omega) hv
    rcases Finset.mem_insert.mp this with h | h
    · subst h; simp
    · have := ih (by omega) v h; omega

theorem keep_mono (hs : ∀ i (hi : i < n), K (i + 1) ⊆ insert ⟨i, hi⟩ (K i)) :
    ∀ j, j ≤ n → ∀ i, i ≤ j → ∀ v ∈ K j, v ∈ K i ∨ i ≤ v.val := by
  intro j
  induction j with
  | zero =>
    intro _ i hi v hv
    left
    have : i = 0 := by omega
    subst this
    exact hv
  | succ j ih =>
    intro hj i hi v hv
    by_cases hij : i = j + 1
    · subst hij; left; exact hv
    · have := hs j (by omega) hv
      rcases Finset.mem_insert.mp this with h | h
      · subst h; right; simp; omega
      · exact ih (by omega) i (by omega) v h

end scan

theorem dead_mono {F : Set (Clause (Fin n))} {K : ℕ → Finset (Fin n)} {i : ℕ}
    {a a2 : Fin n → Bool} (h : Dead F K i a) (hag : ∀ v ∈ K i, a2 v = a v) : Dead F K i a2 := by
  intro a' h'
  exact h a' (fun v hv => (h' v hv).trans (hag v hv))

theorem dead_step {F : Set (Clause (Fin n))} {K : ℕ → Finset (Fin n)}
    (h0 : K 0 = ∅) (hs : ∀ i (hi : i < n), K (i + 1) ⊆ insert ⟨i, hi⟩ (K i))
    {i : ℕ} (hi : i < n) {a : Fin n → Bool} (h : Dead F K i a) (c : Bool)
    (hno : ¬ ∃ C ∈ F, (∀ l ∈ C, l.1 ∈ insert ⟨i, hi⟩ (K i)) ∧
      ¬ ClauseSat (Function.update a ⟨i, hi⟩ c) C) :
    Dead F K (i + 1) (Function.update a ⟨i, hi⟩ c) := by
  classical
  intro a' ha'
  have hlt := keep_lt K h0 hs
  have hmono := keep_mono K hs
  let a'' : Fin n → Bool := fun v =>
    if v ∈ insert (⟨i, hi⟩ : Fin n) (K i) then Function.update a ⟨i, hi⟩ c v else a' v
  have hag : ∀ v ∈ K i, a'' v = a v := by
    intro v hv
    have hvi : v ≠ ⟨i, hi⟩ := by
      intro he; have := hlt i hi.le v hv; rw [he] at this; simp at this
    simp [a'', hv, Function.update_of_ne hvi]
  obtain ⟨j, hij, C, hCF, hCbag, hCun⟩ := h a'' hag
  by_cases hji : j.val = i
  · have hj : j = ⟨i, hi⟩ := Fin.ext hji
    subst hj
    apply absurd hno
    push_neg
    refine ⟨C, hCF, hCbag, ?_⟩
    intro hsat
    apply hCun
    refine (sat_congr ?_).mpr hsat
    intro l hl
    have hm := hCbag l hl
    simp only at hm
    simp only [a'', hm, ite_true]
  · refine ⟨j, by omega, C, hCF, hCbag, ?_⟩
    intro hsat
    apply hCun
    refine (sat_congr ?_).mpr hsat
    intro l hl
    by_cases hvb : l.1 ∈ insert (⟨i, hi⟩ : Fin n) (K i)
    · have hle : l.1.val ≤ i := by
        rcases Finset.mem_insert.mp hvb with h1 | h1
        · rw [h1]
        · have := hlt i hi.le l.1 h1; omega
      have hlj : l.1 ∈ K j.val := by
        rcases Finset.mem_insert.mp (hCbag l hl) with h1 | h1
        · rw [h1] at hle; omega
        · exact h1
      have hk : l.1 ∈ K (i + 1) := by
        rcases hmono j.val j.isLt.le (i + 1) (by omega) l.1 hlj with h1 | h1
        · exact h1
        · omega
      simp only [a'', hvb, ite_true]
      exact (ha' l.1 hk).symm
    · simp only [a'', hvb, ite_false]

/-! ## Runs: lines with held sets -/

/-- The condition on one line `C` written while the clauses `H` are held. -/
def Cond (F : Set (Clause (Fin n))) (w : ℕ) (H : Finset (Clause (Fin n)))
    (C : Clause (Fin n)) : Prop :=
  C.card ≤ 2 * w + 1 ∧ (C ∈ F ∨ ∃ A ∈ H, ∃ B ∈ H, IsResolvent A B C) ∧
    (insert C H).card ≤ 2 * 2 ^ w + w + 3

/-- `Run F w H L H'`: starting with the held clauses `H`, the lines `L` (oldest first) can be
written, ending with the held clauses `H'`. -/
inductive Run (F : Set (Clause (Fin n))) (w : ℕ) :
    Finset (Clause (Fin n)) → List (Clause (Fin n)) → Finset (Clause (Fin n)) → Prop
  | nil (H : Finset (Clause (Fin n))) : Run F w H [] H
  | cons {H G H' : Finset (Clause (Fin n))} {C : Clause (Fin n)} {L : List (Clause (Fin n))} :
      Cond F w H C → G ⊆ insert C H → Run F w G L H' → Run F w H (C :: L) H'

theorem run_snoc {F : Set (Clause (Fin n))} {w : ℕ} {H0 H : Finset (Clause (Fin n))}
    {L : List (Clause (Fin n))} (h : Run F w H0 L H) :
    ∀ (C : Clause (Fin n)) (G : Finset (Clause (Fin n))), Cond F w H C → G ⊆ insert C H →
      Run F w H0 (L ++ [C]) G := by
  induction h with
  | nil H => intro C G hc hg; exact Run.cons hc hg (Run.nil G)
  | cons h1 h2 _ ih => intro C G hc hg; exact Run.cons h1 h2 (ih C G hc hg)

theorem run_drop_ne {F : Set (Clause (Fin n))} {w : ℕ} {H0 H : Finset (Clause (Fin n))}
    {L : List (Clause (Fin n))} (h : Run F w H0 L H) :
    L ≠ [] → ∀ G, G ⊆ H → Run F w H0 L G := by
  induction h with
  | nil H => intro hne; exact absurd rfl hne
  | @cons H G' H' C L hc hg hr ih =>
    intro _ G hG
    by_cases hL : L = []
    · subst hL
      cases hr
      exact Run.cons hc (hG.trans hg) (Run.nil G)
    · exact Run.cons hc hg (ih hL G hG)

theorem run_drop {F : Set (Clause (Fin n))} {w : ℕ} {H : Finset (Clause (Fin n))}
    {L : List (Clause (Fin n))} (h : Run F w ∅ L H) {G : Finset (Clause (Fin n))}
    (hG : G ⊆ H) : Run F w ∅ L G := by
  by_cases hL : L = []
  · subst hL
    cases h
    rw [Finset.subset_empty.mp hG]
    exact Run.nil _
  · exact run_drop_ne h hL G hG

theorem run_deriv {F : Set (Clause (Fin n))} {w : ℕ} {H0 H : Finset (Clause (Fin n))}
    {L : List (Clause (Fin n))} (h : Run F w H0 L H) :
    ∀ π : List (Clause (Fin n)), IsDerivation F π → (∀ x ∈ H0, x ∈ π) →
      IsDerivation F (L.reverse ++ π) ∧ ∀ x ∈ H, x ∈ L.reverse ++ π := by
  induction h with
  | nil H => intro π hπ hs; exact ⟨by simpa using hπ, by simpa using hs⟩
  | @cons H G H' C L hc hg hr ih =>
    intro π hπ hs
    have hd : IsDerivation F (C :: π) := by
      rcases hc.2.1 with h | ⟨A, hA, B, hB, hres⟩
      · exact IsDerivation.ax hπ h
      · exact IsDerivation.res hπ (hs A hA) (hs B hB) hres
    have hs' : ∀ x ∈ G, x ∈ C :: π := by
      intro x hx
      rcases Finset.mem_insert.mp (hg hx) with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hs x h)
    obtain ⟨h1, h2⟩ := ih (C :: π) hd hs'
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact ⟨h1, h2⟩

theorem run_held {F : Set (Clause (Fin n))} {w : ℕ} {H0 H : Finset (Clause (Fin n))}
    {L : List (Clause (Fin n))} (h : Run F w H0 L H) :
    ∃ held : ℕ → Finset (Clause (Fin n)), held 0 = H0 ∧ held L.length = H ∧
      ∀ k (hk : k < L.length), Cond F w (held k) (L.get ⟨k, hk⟩) ∧
        held (k + 1) ⊆ insert (L.get ⟨k, hk⟩) (held k) := by
  induction h with
  | nil H => exact ⟨fun _ => H, rfl, rfl, fun k hk => absurd hk (by simp)⟩
  | @cons H G H' C L hc hg hr ih =>
    obtain ⟨held, h0, h1, h2⟩ := ih
    refine ⟨fun k => if k = 0 then H else held (k - 1), by simp, by simpa using h1, ?_⟩
    intro k hk
    cases k with
    | zero =>
      simp only [if_true]
      refine ⟨by simpa using hc, ?_⟩
      simpa [h0] using hg
    | succ k =>
      have hk' : k < L.length := by simpa using hk
      obtain ⟨h3, h4⟩ := h2 k hk'
      simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
      exact ⟨by simpa using h3, by simpa using h4⟩

/-! ## One memory state, scheduled -/

theorem node {F : Set (Clause (Fin n))} {w : ℕ} {K : ℕ → Finset (Fin n)}
    (h0 : K 0 = ∅) (hs : ∀ i (hi : i < n), K (i + 1) ⊆ insert ⟨i, hi⟩ (K i))
    (hKc : ∀ i, (K i).card ≤ 2 * w)
    {i : ℕ} (hi : i < n) {a : Fin n → Bool} (h : Dead F K i a)
    {L0 : List (Clause (Fin n))} {H0 : Finset (Clause (Fin n))} (hr : Run F w ∅ L0 H0)
    (hb : H0.card + 3 ≤ 2 * 2 ^ w + w + 3) (f : ℕ)
    (prov : ∀ (c : Bool) (L : List (Clause (Fin n))) (H : Finset (Clause (Fin n))),
      Run F w ∅ L H → H0 ⊆ H → H.card ≤ H0.card + 1 →
      Dead F K (i + 1) (Function.update a ⟨i, hi⟩ c) →
      ∃ (L' : List (Clause (Fin n))) (D : Clause (Fin n)), Run F w ∅ L' (insert D H) ∧
        L'.length ≤ L.length + f ∧ Good (K (i + 1)) (Function.update a ⟨i, hi⟩ c) D) :
    ∃ (L' : List (Clause (Fin n))) (D : Clause (Fin n)), Run F w ∅ L' (insert D H0) ∧
      L'.length ≤ L0.length + 2 * f + 3 ∧ Good (K i) a D := by
  classical
  set x : Fin n := ⟨i, hi⟩ with hx
  have hbag : (insert x (K i)).card ≤ 2 * w + 1 :=
    (Finset.card_insert_le _ _).trans (by have := hKc i; omega)
  have branch : ∀ (c : Bool) (L : List (Clause (Fin n))) (H : Finset (Clause (Fin n))),
      Run F w ∅ L H → H0 ⊆ H → H.card ≤ H0.card + 1 →
      ∃ (L' : List (Clause (Fin n))) (E : Clause (Fin n)), Run F w ∅ L' (insert E H) ∧
        L'.length ≤ L.length + f + 1 ∧
        Good (insert x (K i)) (Function.update a x c) E := by
    intro c L H hrun hsub hcard
    by_cases hax : ∃ C ∈ F, (∀ l ∈ C, l.1 ∈ insert x (K i)) ∧
        ¬ ClauseSat (Function.update a x c) C
    · obtain ⟨C, hCF, hCb, hCu⟩ := hax
      have hg : Good (insert x (K i)) (Function.update a x c) C :=
        fun l hl => ⟨hCb l hl, not_sat_iff.mp hCu l hl⟩
      have hci := Finset.card_insert_le C H
      refine ⟨L ++ [C], C, run_snoc hrun C _ ⟨(good_card hg).trans hbag, Or.inl hCF, by omega⟩
        (subset_refl _), by simp, hg⟩
    · have hd := dead_step h0 hs hi h c hax
      obtain ⟨L', D, hr', hl', hg⟩ := prov c L H hrun hsub hcard hd
      refine ⟨L', D, hr', by omega, ?_⟩
      intro l hl
      exact ⟨hs i hi (hg l hl).1, (hg l hl).2⟩
  obtain ⟨L1, E0, hr1, hl1, hg0⟩ := branch false L0 H0 hr (subset_refl _) (by omega)
  obtain ⟨L2, E1, hr2, hl2, hg1⟩ := branch true L1 (insert E0 H0) hr1
    (Finset.subset_insert _ _) (Finset.card_insert_le _ _)
  have reuse : ∀ (c : Bool) (E : Clause (Fin n)), Good (insert x (K i)) (Function.update a x c) E →
      (x, !c) ∉ E → Good (K i) a E := by
    intro c E hg hn l hl
    obtain ⟨h1, h2⟩ := hg l hl
    have hlx : l.1 ≠ x := by
      intro he
      apply hn
      have : l.2 = !c := by
        rw [he, Function.update_self] at h2
        cases c <;> cases hc : l.2 <;> simp_all
      have : l = (x, !c) := Prod.ext he this
      rw [← this]; exact hl
    rw [Function.update_of_ne hlx] at h2
    rcases Finset.mem_insert.mp h1 with h3 | h3
    · exact absurd h3 hlx
    · exact ⟨h3, h2⟩
  have hsub0 : insert E0 H0 ⊆ insert E1 (insert E0 H0) := Finset.subset_insert _ _
  have hsub1 : insert E1 H0 ⊆ insert E1 (insert E0 H0) :=
    Finset.insert_subset_insert _ (Finset.subset_insert _ _)
  by_cases hn0 : (x, true) ∈ E0
  · by_cases hn1 : (x, false) ∈ E1
    · set R := E0.erase (x, true) ∪ E1.erase (x, false) with hR
      have hres : IsResolvent E0 E1 R := ⟨x, hn0, hn1, rfl⟩
      have hgR : Good (K i) a R := by
        intro l hl
        rcases Finset.mem_union.mp hl with hl | hl
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
          refine reuse false (E0.erase (x, true)) ?_ (by simp) l (Finset.mem_erase.mpr ⟨hne, hl⟩)
          intro l' hl'
          exact hg0 l' (Finset.mem_of_mem_erase hl')
        · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
          refine reuse true (E1.erase (x, false)) ?_ (by simp) l (Finset.mem_erase.mpr ⟨hne, hl⟩)
          intro l' hl'
          exact hg1 l' (Finset.mem_of_mem_erase hl')
      have c1 := Finset.card_insert_le R (insert E1 (insert E0 H0))
      have c2 := Finset.card_insert_le E1 (insert E0 H0)
      have c3 := Finset.card_insert_le E0 H0
      have hRc := good_card hgR
      have hKi := hKc i
      have hsubR : insert R H0 ⊆ insert R (insert E1 (insert E0 H0)) :=
        Finset.insert_subset_insert _ ((Finset.subset_insert _ _).trans hsub0)
      refine ⟨L2 ++ [R], R, run_snoc hr2 R _ ⟨by omega, Or.inr ⟨E0, by simp, E1, by simp, hres⟩,
        by omega⟩ hsubR, by simp; omega, hgR⟩
    · exact ⟨L2, E1, run_drop hr2 hsub1, by omega, reuse true E1 hg1 (by simpa using hn1)⟩
  · exact ⟨L2, E0, run_drop hr2 hsub0, by omega, reuse false E0 hg0 (by simpa using hn0)⟩


/-! ## The memory of the cyclic scan -/

/-- Stage `i` remembers the variables below `i` that are opening variables (below `w`) or
among the last `w` ones. -/
def KK (n w : ℕ) : ℕ → Finset (Fin n) := fun i =>
  Finset.univ.filter (fun v : Fin n => v.val < i ∧ (v.val < w ∨ i ≤ v.val + w))

theorem win_card (S : Finset (Fin n)) (lo len : ℕ)
    (h : ∀ v ∈ S, lo ≤ v.val ∧ v.val < lo + len) : S.card ≤ len := by
  have : S.card ≤ (Finset.range len).card := by
    apply Finset.card_le_card_of_injOn (fun v => v.val - lo)
    · intro v hv
      have := h v hv
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro v hv v' hv' he
      have h1 := h v hv
      have h2 := h v' hv'
      simp only at he
      exact Fin.ext (by omega)
  simpa using this

theorem KK_zero {w : ℕ} : KK n w 0 = ∅ := by
  ext v
  simp [KK]

theorem KK_succ {w : ℕ} : ∀ i (hi : i < n), KK n w (i + 1) ⊆ insert ⟨i, hi⟩ (KK n w i) := by
  intro i hi v hv
  simp only [KK, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rw [Finset.mem_insert]
  by_cases h : v.val = i
  · left; exact Fin.ext h
  · right
    simp only [KK, Finset.mem_filter, Finset.mem_univ, true_and]
    omega

theorem KK_card {w : ℕ} : ∀ i, (KK n w i).card ≤ 2 * w := by
  intro i
  have hsub : KK n w i ⊆ (Finset.univ.filter (fun v : Fin n => v.val < w)) ∪
      (Finset.univ.filter (fun v : Fin n => i ≤ v.val + w ∧ v.val < i)) := by
    intro v hv
    simp only [KK, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have c1 : (Finset.univ.filter (fun v : Fin n => v.val < w)).card ≤ w := by
    apply win_card _ 0 w
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    omega
  have c2 : (Finset.univ.filter (fun v : Fin n => i ≤ v.val + w ∧ v.val < i)).card ≤ w := by
    apply win_card _ (i - w) w
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    omega
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

/-- The memory state with opening `a` and recent part `T`. -/
def st (w : ℕ) (a : Fin n → Bool) (T : Finset (Fin n)) : Fin n → Bool :=
  fun v => if v.val < min w n then a v else decide (v ∈ T)

/-- `Lay` serves every dead state of stage `i` that has the opening of `a`. -/
def Inv (F : Set (Clause (Fin n))) (w i : ℕ) (a : Fin n → Bool)
    (Lay : Finset (Clause (Fin n))) : Prop :=
  ∀ a' : Fin n → Bool, (∀ v : Fin n, v.val < min w n → a' v = a v) →
    Dead F (KK n w) i a' → ∃ D ∈ Lay, Good (KK n w i) a' D

/-! ## One layer of the dynamic program for a fixed opening -/

theorem states {F : Set (Clause (Fin n))} {w i : ℕ} (hmi : min w n ≤ i) (hi : i < n)
    (a : Fin n → Bool) (B Lay : Finset (Clause (Fin n))) (hLB : Lay ⊆ B)
    (hBc : B.card ≤ 2 ^ w + w) (hInv : Inv F w (i + 1) a Lay) :
    ∀ (Ts : List (Finset (Fin n))) (Acc : Finset (Clause (Fin n))) (L : List (Clause (Fin n))),
      Run F w ∅ L (B ∪ Acc) → Acc.card + Ts.length ≤ 2 ^ w →
      ∃ (L' : List (Clause (Fin n))) (Acc' : Finset (Clause (Fin n))),
        Run F w ∅ L' (B ∪ Acc') ∧ L'.length ≤ L.length + 3 * Ts.length ∧
        Acc ⊆ Acc' ∧ Acc'.card ≤ Acc.card + Ts.length ∧
        ∀ T ∈ Ts, Dead F (KK n w) i (st w a T) → ∃ D ∈ Acc', Good (KK n w i) (st w a T) D := by
  classical
  intro Ts
  induction Ts with
  | nil =>
    intro Acc L hr _
    exact ⟨L, Acc, hr, by simp, subset_refl _, by simp, by simp⟩
  | cons T Ts ih =>
    intro Acc L hr hc
    simp only [List.length_cons] at hc
    by_cases hd : Dead F (KK n w) i (st w a T)
    · have hcu := Finset.card_union_le B Acc
      obtain ⟨L1, D, hr1, hl1, hg⟩ := node KK_zero KK_succ KK_card hi hd hr (by omega) 0 (by
        intro c L2 H hr2 hBH _ hd'
        have hag : ∀ v : Fin n, v.val < min w n →
            Function.update (st w a T) ⟨i, hi⟩ c v = a v := by
          intro v hv
          have hne : v ≠ ⟨i, hi⟩ := by
            intro he
            rw [he] at hv
            exact absurd hv (by show ¬ (i < min w n); omega)
          rw [Function.update_of_ne hne]
          show (if v.val < min w n then a v else decide (v ∈ T)) = a v
          rw [if_pos hv]
        obtain ⟨D, hD, hgD⟩ := hInv _ hag hd'
        have hDH : D ∈ H := hBH (Finset.mem_union_left _ (hLB hD))
        exact ⟨L2, D, by rwa [Finset.insert_eq_of_mem hDH], by omega, hgD⟩)
      rw [← Finset.union_insert] at hr1
      have hci := Finset.card_insert_le D Acc
      obtain ⟨L', Acc', hr', hl', hsub, hcard, hcov⟩ := ih (insert D Acc) L1 hr1 (by omega)
      refine ⟨L', Acc', hr', by simp; omega, (Finset.subset_insert _ _).trans hsub,
        by simp only [List.length_cons]; omega, ?_⟩
      intro T' hT' hd'
      rcases List.mem_cons.mp hT' with h | h
      · subst h; exact ⟨D, hsub (Finset.mem_insert_self _ _), hg⟩
      · exact hcov T' h hd'
    · obtain ⟨L', Acc', hr', hl', hsub, hcard, hcov⟩ := ih Acc L hr (by omega)
      refine ⟨L', Acc', hr', by simp; omega, hsub, by simp only [List.length_cons]; omega, ?_⟩
      intro T' hT' hd'
      rcases List.mem_cons.mp hT' with h | h
      · subst h; exact absurd hd' hd
      · exact hcov T' h hd'

theorem stage {F : Set (Clause (Fin n))} {w i : ℕ} (hmi : min w n ≤ i) (hi : i < n)
    (a : Fin n → Bool) {L : List (Clause (Fin n))} {P Lay : Finset (Clause (Fin n))}
    (hr : Run F w ∅ L (P ∪ Lay)) (hP : P.card ≤ w) (hLc : Lay.card ≤ 2 ^ w)
    (hInv : Inv F w (i + 1) a Lay) :
    ∃ (L' : List (Clause (Fin n))) (Lay' : Finset (Clause (Fin n))),
      Run F w ∅ L' (P ∪ Lay') ∧ L'.length ≤ L.length + 3 * 2 ^ w ∧
      Lay'.card ≤ 2 ^ w ∧ Inv F w i a Lay' := by
  classical
  set Rs := (KK n w i).filter (fun v => min w n ≤ v.val) with hRs
  have hRc : Rs.card ≤ w := by
    apply win_card Rs (i - w) w
    intro v hv
    simp only [Rs, KK, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have := v.isLt
    omega
  have hpow : 2 ^ Rs.card ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hRc
  have hlen : Rs.powerset.toList.length = 2 ^ Rs.card := by
    rw [Finset.length_toList, Finset.card_powerset]
  have hcu := Finset.card_union_le P Lay
  obtain ⟨L', Acc', hr', hl', -, hcard, hcov⟩ :=
    states hmi hi a (P ∪ Lay) Lay (fun x hx => Finset.mem_union_right _ hx) (by omega) hInv
      Rs.powerset.toList ∅ L (by simpa using hr) (by simp only [Finset.card_empty]; omega)
  have hsub : P ∪ Acc' ⊆ (P ∪ Lay) ∪ Acc' := by
    intro x hx
    simp only [Finset.mem_union] at hx ⊢
    tauto
  refine ⟨L', Acc', run_drop hr' hsub, by omega, by simp only [Finset.card_empty] at hcard; omega,
    ?_⟩
  intro a' hag hd
  set T := Rs.filter (fun v => a' v = true) with hT
  have hagT : ∀ v ∈ KK n w i, st w a T v = a' v := by
    intro v hv
    by_cases hvm : v.val < min w n
    · show (if v.val < min w n then a v else decide (v ∈ T)) = a' v
      rw [if_pos hvm]
      exact (hag v hvm).symm
    · have hvR : v ∈ Rs := Finset.mem_filter.mpr ⟨hv, by omega⟩
      show (if v.val < min w n then a v else decide (v ∈ T)) = a' v
      rw [if_neg hvm]
      simp only [T, Finset.mem_filter, hvR, true_and]
      cases a' v <;> simp
  have hTm : T ∈ Rs.powerset.toList := by
    rw [Finset.mem_toList, Finset.mem_powerset]
    exact Finset.filter_subset _ _
  obtain ⟨D, hD, hg⟩ := hcov T hTm (dead_mono hd hagT)
  refine ⟨D, hD, fun l hl => ⟨(hg l hl).1, ?_⟩⟩
  have := (hg l hl).2
  rw [hagT l.1 (hg l hl).1] at this
  exact this

theorem dp {F : Set (Clause (Fin n))} {w : ℕ} (a : Fin n → Bool) :
    ∀ k i, i + k = n → min w n ≤ i →
      ∀ (L : List (Clause (Fin n))) (P : Finset (Clause (Fin n))),
      Run F w ∅ L P → P.card ≤ w →
      ∃ (L' : List (Clause (Fin n))) (Lay : Finset (Clause (Fin n))),
        Run F w ∅ L' (P ∪ Lay) ∧ L'.length ≤ L.length + 3 * k * 2 ^ w ∧
        Lay.card ≤ 2 ^ w ∧ Inv F w i a Lay := by
  intro k
  induction k with
  | zero =>
    intro i hik _ L P hr _
    refine ⟨L, ∅, by simpa using hr, by simp, by simp, ?_⟩
    intro a' _ hd
    obtain ⟨j, hj, _⟩ := hd a' (fun _ _ => rfl)
    have := j.isLt
    omega
  | succ k ih =>
    intro i hik hmi L P hr hP
    obtain ⟨L1, Lay1, hr1, hl1, hc1, hI1⟩ := ih (i + 1) (by omega) (by omega) L P hr hP
    obtain ⟨L2, Lay2, hr2, hl2, hc2, hI2⟩ := stage hmi (by omega) a hr1 hP hc1 hI1
    refine ⟨L2, Lay2, hr2, ?_, hc2, hI2⟩
    have e : 3 * (k + 1) * 2 ^ w = 3 * k * 2 ^ w + 3 * 2 ^ w := by ring
    rw [e]
    omega

/-! ## Depth-first search over the opening -/

theorem dfs {F : Set (Clause (Fin n))} {w : ℕ} :
    ∀ k i, i + k = min w n → ∀ a : Fin n → Bool, Dead F (KK n w) i a →
      ∀ (L : List (Clause (Fin n))) (P : Finset (Clause (Fin n))), Run F w ∅ L P →
      P.card ≤ i →
      ∃ (L' : List (Clause (Fin n))) (D : Clause (Fin n)), Run F w ∅ L' (insert D P) ∧
        L'.length + 3 ≤ L.length + 2 ^ k * (3 * (n - min w n) * 2 ^ w + 3) ∧
        Good (KK n w i) a D := by
  intro k
  induction k with
  | zero =>
    intro i hik a hd L P hr hP
    have hi : i = min w n := by omega
    subst hi
    obtain ⟨L1, Lay, hr1, hl1, _, hI⟩ :=
      dp a (n - min w n) (min w n) (by omega) le_rfl L P hr (by omega)
    obtain ⟨D, hD, hg⟩ := hI a (fun _ _ => rfl) hd
    have hsub : insert D P ⊆ P ∪ Lay := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact Finset.mem_union_right _ hD
      · exact Finset.mem_union_left _ h
    refine ⟨L1, D, run_drop hr1 hsub, ?_, hg⟩
    rw [pow_zero, one_mul]
    omega
  | succ k ih =>
    intro i hik a hd L P hr hP
    have hi : i < n := by omega
    set Y := 2 ^ k * (3 * (n - min w n) * 2 ^ w + 3) with hY
    have hX : 3 ≤ Y := le_trans (by omega)
      (Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) k))
    obtain ⟨L', D, hr', hl', hg⟩ := node KK_zero KK_succ KK_card hi hd hr (by omega) (Y - 3) (by
      intro c L1 H hr1 hPH hHc hd'
      obtain ⟨L2, D, hr2, hl2, hg2⟩ := ih (i + 1) (by omega) _ hd' L1 H hr1 (by omega)
      exact ⟨L2, D, hr2, by omega, hg2⟩)
    refine ⟨L', D, hr', ?_, hg⟩
    have e : 2 ^ (k + 1) * (3 * (n - min w n) * 2 ^ w + 3) = 2 * Y := by rw [hY]; ring
    rw [e]
    omega

/-! ## Clauses live at their greatest variable -/

theorem modcase {x m : ℕ} (h : x < 2 * m) :
    (x < m ∧ x % m = x) ∨ (m ≤ x ∧ x % m = x - m) := by
  by_cases hx : x < m
  · exact Or.inl ⟨hx, Nat.mod_eq_of_lt hx⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bags {w : ℕ} (hn : 0 < n) {F : Set (Clause (Fin n))}
    (hF : ∀ D ∈ F, ∃ start : Fin n, ∀ lit ∈ D, ∃ offset : Fin (w + 1),
      lit.1.val = (start.val + offset.val) % n) :
    ∀ C ∈ F, ∃ j : Fin n, ∀ l ∈ C, l.1 ∈ insert j (KK n w j.val) := by
  classical
  intro C hC
  obtain ⟨s, hs⟩ := hF C hC
  by_cases hne : C.Nonempty
  · have hne' : (C.image (fun l : Literal (Fin n) => l.1)).Nonempty := hne.image _
    refine ⟨(C.image (fun l : Literal (Fin n) => l.1)).max' hne', ?_⟩
    intro l hl
    have hle : l.1 ≤ (C.image (fun l : Literal (Fin n) => l.1)).max' hne' :=
      Finset.le_max' _ _ (Finset.mem_image_of_mem _ hl)
    obtain ⟨l', hl', hl'J⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne')
    rcases eq_or_lt_of_le hle with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      simp only [KK, Finset.mem_filter, Finset.mem_univ, true_and]
      have hlt : l.1.val < ((C.image (fun l : Literal (Fin n) => l.1)).max' hne').val := h
      rw [← hl'J] at hlt ⊢
      refine ⟨hlt, ?_⟩
      by_cases hwn : n ≤ w
      · left; have := l.1.isLt; omega
      · obtain ⟨o1, ho1⟩ := hs l hl
        obtain ⟨o2, ho2⟩ := hs l' hl'
        have := o1.isLt
        have := o2.isLt
        have := s.isLt
        rcases modcase (x := s.val + o1.val) (m := n) (by omega) with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
        rcases modcase (x := s.val + o2.val) (m := n) (by omega) with ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
        · rw [b1] at ho1
          rw [b2] at ho2
          omega
  · refine ⟨⟨0, hn⟩, ?_⟩
    intro l hl
    exact absurd ⟨l, hl⟩ hne

theorem arith (n w : ℕ) (hn : 0 < n) :
    2 ^ min w n * (3 * (n - min w n) * 2 ^ w + 3) ≤ 3 * n * 4 ^ w + 4 := by
  have h4 : (4 : ℕ) ^ w = 2 ^ w * 2 ^ w := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  have hq : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  rw [h4]
  rcases le_total w n with h | h
  · rw [min_eq_left h]
    obtain ⟨d, rfl⟩ : ∃ d, n = w + d := ⟨n - w, by omega⟩
    rw [show w + d - w = d by omega]
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw
      simp
    · have h1 : 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.le_mul_of_pos_left _ (by omega)
      have h2 : 2 ^ w * 2 ^ w ≤ w * (2 ^ w * 2 ^ w) := Nat.le_mul_of_pos_left _ hw
      nlinarith
  · rw [min_eq_right h, Nat.sub_self]
    have h1 : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) h
    have h2 : 2 ^ w ≤ 2 ^ w * 2 ^ w := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 2 ^ w * 2 ^ w ≤ n * (2 ^ w * 2 ^ w) := Nat.le_mul_of_pos_left _ hn
    nlinarith

end PEqualNP.Outside.L_pcx_225

open PEqualNP.Outside.L_pcx_225 in
theorem PEqualNP.Outside.L_pcx_225 : ∀ (n w : ℕ), 0 < n →
  ∀ F : Set (PEqualNP.ProofComplexity.Clause (Fin n)),
    (∀ D ∈ F, ∃ start : Fin n, ∀ lit ∈ D, ∃ offset : Fin (w + 1),
      lit.1.val = (start.val + offset.val) % n) →
    ¬ PEqualNP.ProofComplexity.Satisfiable F →
    ∃ (t : ℕ) (line : Fin t → PEqualNP.ProofComplexity.Clause (Fin n))
      (held : ℕ → Finset (PEqualNP.ProofComplexity.Clause (Fin n))),
      t ≤ 3 * n * 4 ^ w + 1 ∧ held 0 = ∅ ∧
      (∅ : PEqualNP.ProofComplexity.Clause (Fin n)) ∈ held t ∧
      PEqualNP.ProofComplexity.IsRefutation F (List.ofFn line).reverse ∧
      ∀ k : Fin t,
        let H := held k.val
        let C := line k
        C.card ≤ 2 * w + 1 ∧
        (C ∈ F ∨ ∃ A ∈ H, ∃ B ∈ H, PEqualNP.ProofComplexity.IsResolvent A B C) ∧
        (insert C H).card ≤ 2 * 2 ^ w + w + 3 ∧
        held (k.val + 1) ⊆ insert C H := by
  intro n w hn F hF hun
  classical
  have hbags := bags hn hF
  have hdead : Dead F (KK n w) 0 (fun _ => false) := by
    intro a' _
    have : ¬ PEqualNP.ProofComplexity.Satisfies a' F := fun h => hun ⟨a', h⟩
    unfold PEqualNP.ProofComplexity.Satisfies at this
    push_neg at this
    obtain ⟨C, hCF, hCu⟩ := this
    obtain ⟨j, hj⟩ := hbags C hCF
    exact ⟨j, Nat.zero_le _, C, hCF, hj, hCu⟩
  obtain ⟨L, D, hr, hl, hg⟩ :=
    dfs (min w n) 0 (by omega) _ hdead [] ∅ (Run.nil ∅) (by simp)
  have hDe : D = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro l hl
    have := (hg l hl).1
    rw [KK_zero] at this
    simp at this
  subst hDe
  obtain ⟨held, h0, ht, hstep⟩ := run_held hr
  obtain ⟨hd1, hd2⟩ := run_deriv hr [] PEqualNP.ProofComplexity.IsDerivation.nil (by simp)
  have har := arith n w hn
  refine ⟨L.length, L.get, held, ?_, h0, ?_, ?_, ?_⟩
  · simp at hl
    omega
  · rw [ht]; exact Finset.mem_insert_self _ _
  · rw [List.ofFn_get]
    refine ⟨by simpa using hd1, ?_⟩
    have := hd2 ∅ (Finset.mem_insert_self _ _)
    simpa using this
  · intro k
    obtain ⟨h1, h2⟩ := hstep k.val k.isLt
    exact ⟨h1.1, h1.2.1, h1.2.2, h2⟩
