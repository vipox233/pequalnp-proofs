import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_679

private def flipAt {n : ℕ} (i : Fin n) (w : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = i then !w i else w j

private lemma flipAt_invol {n : ℕ} (i : Fin n) (w : Fin n → Bool) :
    flipAt i (flipAt i w) = w := by
  funext j
  dsimp only [flipAt]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

private lemma card_filter_eq_half {n : ℕ} (P : (Fin n → Bool) → Prop) [DecidablePred P]
    (i : Fin n) (hflip : ∀ w, P (flipAt i w) ↔ ¬ P w) :
    2 * ((Finset.univ : Finset (Fin n → Bool)).filter P).card = 2 ^ n := by
  have hbij : ((Finset.univ : Finset (Fin n → Bool)).filter P).card =
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => ¬ P w)).card := by
    refine Finset.card_bij (fun w _ => flipAt i w) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact fun h => ((hflip w).1 h) hw
    · intro w1 _ w2 _ heq
      have := congrArg (flipAt i) heq
      simpa [flipAt_invol] using this
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨flipAt i w, ?_, flipAt_invol i w⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hflip w).2 hw
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Bool))) P
  have huniv : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  omega

private lemma card_filter_agree {n : ℕ} (S : Finset (Fin n)) (σ : Fin n → Bool) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => ∀ i ∈ S, w i = σ i)).card =
      2 ^ (n - S.card) := by
  have hcomp : (Finset.univ \ S).card = n - S.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [← hcomp, ← Finset.card_powerset]
  refine Finset.card_bij (fun w _ => (Finset.univ \ S).filter (fun i => w i = true)) ?_ ?_ ?_
  · intro w _
    rw [Finset.mem_powerset]
    exact Finset.filter_subset _ _
  · intro w1 h1 w2 h2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    funext i
    by_cases hi : i ∈ S
    · rw [h1 i hi, h2 i hi]
    · have hiU : i ∈ Finset.univ \ S := Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hi⟩
      have hiff := Finset.ext_iff.1 heq i
      simp only [Finset.mem_filter, hiU, true_and] at hiff
      cases h1i : w1 i <;> cases h2i : w2 i <;> simp_all
  · intro T hT
    rw [Finset.mem_powerset] at hT
    refine ⟨fun i => if i ∈ S then σ i else decide (i ∈ T), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi; simp [hi]
    · ext i
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hiS, hdec⟩
        simp only [hiS, ite_false, decide_eq_true_eq] at hdec
        exact hdec
      · intro hiT
        have hiS : i ∉ S := (Finset.mem_sdiff.1 (hT hiT)).2
        exact ⟨hiS, by simp [hiS, hiT]⟩

private def runHist {W : Type*} (satA : W → Bool) (askS : List Bool → W) : ℕ → List Bool
  | 0 => []
  | t + 1 =>
    let past := runHist satA askS t
    past ++ [satA (askS past)]

private lemma foldl_range_eq_runHist {W : Type*} (satA : W → Bool) (askS : List Bool → W) (q : ℕ) :
    (List.range q).foldl (fun (past : List Bool) _ => past ++ [satA (askS past)]) [] =
      runHist satA askS q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rfl

private lemma runHist_eq_of_sat_eq {W : Type*} (satA satB : W → Bool) (askS : List Bool → W) (q : ℕ)
    (hagree : ∀ t < q, satA (askS (runHist satB askS t)) = satB (askS (runHist satB askS t))) :
    runHist satA askS q = runHist satB askS q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have hprev : runHist satA askS q = runHist satB askS q :=
      ih (fun t ht => hagree t (Nat.lt_succ_of_lt ht))
    dsimp only [runHist]
    rw [hprev, hagree q (Nat.lt_succ_self q)]

private lemma distinct_signed_columns {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : β → α → Bool)
    (h1 : ∀ a : α, (∃ b, M b a = true) ∧ (∃ b, M b a = false))
    (h2 : ∀ a1 a2 : α, a1 ≠ a2 → (∃ b, M b a1 ≠ M b a2) ∧ (∃ b, M b a1 = M b a2))
    (hne : Nonempty α) :
    2 * Fintype.card α + 2 ≤ 2 ^ Fintype.card β := by
  obtain ⟨a0⟩ := hne
  obtain ⟨b0, _⟩ := (h1 a0).1
  let f : (α × Bool) ⊕ Bool → (β → Bool) := fun x =>
    match x with
    | Sum.inl (a, s) => fun b => if s then !(M b a) else M b a
    | Sum.inr c => fun _ => c
  have hfinj : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl p1 =>
      rcases p1 with ⟨a1, s1⟩
      cases y with
      | inl p2 =>
        rcases p2 with ⟨a2, s2⟩
        dsimp only [f] at hxy
        by_cases ha : a1 = a2
        · subst ha
          have hb := congrFun hxy b0
          cases s1 <;> cases s2 <;> cases hM : M b0 a1 <;> simp_all
        · by_cases hs : s1 = s2
          · subst hs
            obtain ⟨b, hb⟩ := (h2 a1 a2 ha).1
            have h := congrFun hxy b
            cases s1 <;> cases hM1 : M b a1 <;> cases hM2 : M b a2 <;> simp_all
          · obtain ⟨b, hb⟩ := (h2 a1 a2 ha).2
            have h := congrFun hxy b
            cases s1 <;> cases s2 <;> cases hM1 : M b a1 <;> cases hM2 : M b a2 <;> simp_all
      | inr c =>
        dsimp only [f] at hxy
        obtain ⟨b1, hb1⟩ := (h1 a1).1
        obtain ⟨b2, hb2⟩ := (h1 a1).2
        have e1 := congrFun hxy b1
        have e2 := congrFun hxy b2
        rw [hb1] at e1; rw [hb2] at e2
        cases s1 <;> cases c <;> simp at e1 e2
    | inr c1 =>
      cases y with
      | inl p2 =>
        rcases p2 with ⟨a2, s2⟩
        dsimp only [f] at hxy
        obtain ⟨b1, hb1⟩ := (h1 a2).1
        obtain ⟨b2, hb2⟩ := (h1 a2).2
        have e1 := congrFun hxy b1
        have e2 := congrFun hxy b2
        rw [hb1] at e1; rw [hb2] at e2
        cases s2 <;> cases c1 <;> simp at e1 e2
      | inr c2 =>
        dsimp only [f] at hxy
        have hb := congrFun hxy b0
        exact congrArg Sum.inr hb
  have hle := Fintype.card_le_of_injective f hfinj
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fun] at hle
  omega

end PEqualNP.Outside.L_lib_679

theorem PEqualNP.Outside.L_lib_679 : ∀ (n s : ℕ), 3 ≤ s → s ≤ n →
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let count := fun (G : F) => (Finset.univ.filter (fun u => sat G u = true)).card
  let Q := 2 ^ n
  ∀ (M q fp fn : ℕ), fp + fn < M →
    ∀ (ask : Fin M → List Bool → W) (report : Fin M → List Bool → Bool),
      let yes := fun (A : F) => (Finset.univ.filter (fun seed : Fin M =>
        let history := (List.range q).foldl (fun (past : List Bool) _ =>
          past ++ [sat A (ask seed past)]) []
        report seed history = true)).card
      (∀ A : F, 2 * count A ≤ Q → yes A ≤ fp) →
      (∀ A : F, Q * (2 ^ (s - 1) + 1) ≤ 2 ^ s * count A → M ≤ yes A + fn) →
      2 ^ (s - 1) * (M - fp - fn) ≤ q * (M - fp) ∧
      (fn = 0 → 2 ^ (s - 3) * Nat.clog 2 (2 * (n - s + 2) + 2) ≤ q) ∧
      (fp = 0 → 2 * n + 2 ≤ 2 ^ q) := by
  intro n s hs3 hsn W Lit F sat count Q M q fp fn hfpfn ask report yes hlow hhigh
  have hsat_iff : ∀ (C : F) (w : W),
      sat C w = true ↔ ∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2 := by
    intro C w; dsimp only [sat]; exact decide_eq_true_iff
  let baseF : Fin n → Bool → F := fun c0 b0 => {((c0, b0), (c0, b0))}
  have hsat_base : ∀ (c0 : Fin n) (b0 : Bool) (w : W),
      sat (baseF c0 b0) w = true ↔ w c0 ≠ b0 := by
    intro c0 b0 w
    rw [hsat_iff]
    constructor
    · intro h
      have h1 := h ((c0, b0), (c0, b0)) (Finset.mem_singleton_self _)
      rcases h1 with h1 | h1 <;> exact h1
    · intro h c hc
      rw [Finset.mem_singleton.1 hc]
      exact Or.inl h
  have hcount_base : ∀ (c0 : Fin n) (b0 : Bool), 2 * count (baseF c0 b0) = Q := by
    intro c0 b0
    dsimp only [count, Q]
    have hfilt : (Finset.univ : Finset W).filter (fun u => sat (baseF c0 b0) u = true) =
        (Finset.univ : Finset W).filter (fun u => u c0 ≠ b0) := by
      ext u; simp [hsat_base]
    rw [hfilt]
    refine PEqualNP.Outside.L_lib_679.card_filter_eq_half (fun u => u c0 ≠ b0) c0 (fun w => ?_)
    simp only [PEqualNP.Outside.L_lib_679.flipAt, ite_true]
    cases w c0 <;> cases b0 <;> simp
  let starF : Fin n → Bool → Finset (Fin n) → (Fin n → Bool) → F :=
    fun c0 b0 L σ => L.image (fun ℓ => ((c0, b0), (ℓ, !(σ ℓ))))
  have hsat_star : ∀ (c0 : Fin n) (b0 : Bool) (L : Finset (Fin n)) (σ : Fin n → Bool) (w : W),
      sat (starF c0 b0 L σ) w = true ↔ (w c0 ≠ b0 ∨ ∀ ℓ ∈ L, w ℓ = σ ℓ) := by
    intro c0 b0 L σ w
    rw [hsat_iff]
    constructor
    · intro hall
      by_cases hc : w c0 = b0
      · right
        intro ℓ hℓ
        have h := hall ((c0, b0), (ℓ, !(σ ℓ))) (Finset.mem_image.2 ⟨ℓ, hℓ, rfl⟩)
        rcases h with h1 | h2
        · exact absurd hc h1
        · cases hw : w ℓ <;> cases hσ : σ ℓ <;> simp_all
      · left; exact hc
    · rintro (hc | hL) c hc_mem
      · obtain ⟨ℓ, _, rfl⟩ := Finset.mem_image.1 hc_mem
        left; exact hc
      · obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.1 hc_mem
        right
        have h := hL ℓ hℓ
        rw [h]
        cases σ ℓ <;> simp
  have hcount_star : ∀ (c0 : Fin n) (b0 : Bool) (L : Finset (Fin n)) (σ : Fin n → Bool),
      c0 ∉ L → L.card = s - 1 →
      Q * (2 ^ (s - 1) + 1) ≤ 2 ^ s * count (starF c0 b0 L σ) := by
    intro c0 b0 L σ hcL hLcard
    have hset : (Finset.univ : Finset W).filter (fun u => sat (starF c0 b0 L σ) u = true) =
        ((Finset.univ : Finset W).filter (fun u => u c0 ≠ b0)) ∪
        ((Finset.univ : Finset W).filter (fun u => ∀ i ∈ insert c0 L, u i = if i = c0 then b0 else σ i)) := by
      ext u
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hsat_star,
        Finset.mem_insert]
      constructor
      · rintro (hc | hL)
        · left; exact hc
        · by_cases hcu : u c0 = b0
          · right
            intro i hi
            rcases hi with rfl | hiL
            · simp [hcu]
            · have hne : i ≠ c0 := fun h => hcL (h ▸ hiL)
              simp [hne, hL i hiL]
          · left; exact hcu
      · rintro (hc | hall)
        · left; exact hc
        · right
          intro ℓ hℓ
          have hne : ℓ ≠ c0 := fun h => hcL (h ▸ hℓ)
          have h := hall ℓ (Or.inr hℓ)
          simpa [hne] using h
    have hdisj : Disjoint
        ((Finset.univ : Finset W).filter (fun u => u c0 ≠ b0))
        ((Finset.univ : Finset W).filter (fun u => ∀ i ∈ insert c0 L, u i = if i = c0 then b0 else σ i)) := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      have := h2 c0 (Finset.mem_insert_self c0 L)
      simp only [ite_true] at this
      exact h1 this
    have hc1 : ((Finset.univ : Finset W).filter (fun u => u c0 ≠ b0)).card = 2 ^ (n - 1) := by
      have heq : (Finset.univ : Finset W).filter (fun u => u c0 ≠ b0) =
          (Finset.univ : Finset W).filter (fun u => ∀ i ∈ ({c0} : Finset (Fin n)), u i = !b0) := by
        ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro h i rfl; cases hu : u i <;> cases hb : b0 <;> simp_all
        · intro h; have := h c0 rfl; cases hu : u c0 <;> cases hb : b0 <;> simp_all
      rw [heq, PEqualNP.Outside.L_lib_679.card_filter_agree, Finset.card_singleton]
    have hc2 : ((Finset.univ : Finset W).filter
        (fun u => ∀ i ∈ insert c0 L, u i = if i = c0 then b0 else σ i)).card = 2 ^ (n - s) := by
      rw [PEqualNP.Outside.L_lib_679.card_filter_agree, Finset.card_insert_of_notMem hcL, hLcard,
        show s - 1 + 1 = s by omega]
    have hcnt : count (starF c0 b0 L σ) = 2 ^ (n - 1) + 2 ^ (n - s) := by
      dsimp only [count]
      rw [hset, Finset.card_union_of_disjoint hdisj, hc1, hc2]
    rw [hcnt]
    dsimp only [Q]
    rw [mul_add, mul_add, mul_one, ← pow_add, ← pow_add, ← pow_add]
    have e1 : s + (n - 1) = n + (s - 1) := by omega
    have e2 : s + (n - s) = n := by omega
    rw [e1, e2]
  have hyes_hist : ∀ A : F, yes A =
      ((Finset.univ : Finset (Fin M)).filter (fun seed : Fin M =>
        report seed (PEqualNP.Outside.L_lib_679.runHist (sat A) (ask seed) q) = true)).card := by
    intro A
    dsimp only [yes]
    congr 1; ext seed
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      PEqualNP.Outside.L_lib_679.foldl_range_eq_runHist]
  let c0 : Fin n := ⟨0, by omega⟩
  let b0 : Bool := false
  let B : F := baseF c0 b0
  have hyesB : yes B ≤ fp := hlow B (by rw [hcount_base])
  let Rej : Finset (Fin M) :=
    (Finset.univ : Finset (Fin M)).filter (fun seed : Fin M =>
      report seed (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed) q) = false)
  have hRej_add : yes B + Rej.card = M := by
    rw [hyes_hist B]
    have hnot : Rej = (Finset.univ : Finset (Fin M)).filter (fun seed : Fin M =>
        ¬ (report seed (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed) q) = true)) := by
      ext seed; simp [Rej]
    rw [hnot, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hRej_ge : M - fp ≤ Rej.card := by omega
  have hRej_pos : 0 < Rej.card := by omega
  have hhit_star : ∀ (L : Finset (Fin n)) (P : Finset (Fin n)) (seed : Fin M),
      seed ∈ Rej →
      report seed (PEqualNP.Outside.L_lib_679.runHist (sat (starF c0 b0 L (fun ℓ => decide (ℓ ∈ P)))) (ask seed) q) = true →
      ∃ t : Fin q,
        let w := ask seed (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed) t.val)
        w c0 = b0 ∧ L.filter (fun ℓ => w ℓ = true) = P ∩ L := by
    intro L P seed hseed hacc
    have hrej : report seed (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed) q) = false :=
      (Finset.mem_filter.1 hseed).2
    by_contra hno
    push Not at hno
    have hagree : ∀ t < q,
        sat (starF c0 b0 L (fun ℓ => decide (ℓ ∈ P)))
          (ask seed (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed) t)) =
        sat B (ask seed (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed) t)) := by
      intro t ht
      set w := ask seed (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed) t)
      by_cases hwc : w c0 = b0
      · have hBfalse : sat B w = false := by
          cases h : sat B w
          · rfl
          · exact absurd hwc ((hsat_base c0 b0 w).1 h)
        have hSfalse : sat (starF c0 b0 L (fun ℓ => decide (ℓ ∈ P))) w = false := by
          cases h : sat (starF c0 b0 L (fun ℓ => decide (ℓ ∈ P))) w
          · rfl
          · rcases (hsat_star c0 b0 L (fun ℓ => decide (ℓ ∈ P)) w).1 h with hne | hall
            · exact absurd hwc hne
            · exfalso
              apply hno ⟨t, ht⟩
              refine ⟨hwc, ?_⟩
              ext ℓ
              simp only [Finset.mem_filter, Finset.mem_inter]
              constructor
              · rintro ⟨hℓL, hwℓ⟩
                change w ℓ = true at hwℓ
                have hdec := hall ℓ hℓL
                rw [hwℓ] at hdec
                exact ⟨of_decide_eq_true hdec.symm, hℓL⟩
              · rintro ⟨hℓP, hℓL⟩
                refine ⟨hℓL, ?_⟩
                change w ℓ = true
                rw [hall ℓ hℓL]; simp [hℓP]
        rw [hBfalse, hSfalse]
      · have hBtrue : sat B w = true := (hsat_base c0 b0 w).2 hwc
        have hStrue : sat (starF c0 b0 L (fun ℓ => decide (ℓ ∈ P))) w = true :=
          (hsat_star c0 b0 L (fun ℓ => decide (ℓ ∈ P)) w).2 (Or.inl hwc)
        rw [hBtrue, hStrue]
    have heq := PEqualNP.Outside.L_lib_679.runHist_eq_of_sat_eq
      (sat (starF c0 b0 L (fun ℓ => decide (ℓ ∈ P)))) (sat B) (ask seed) q hagree
    rw [heq, hrej] at hacc
    exact Bool.false_ne_true hacc
  have hpart1 : 2 ^ (s - 1) * (M - fp - fn) ≤ q * (M - fp) := by
    let L0 : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => 1 ≤ i.val ∧ i.val < s)
    have hc0_L0 : c0 ∉ L0 := by simp [L0, c0]
    have hL0_card : L0.card = s - 1 := by
      rw [← Finset.card_range (s - 1)]
      refine Finset.card_bij (fun i _ => i.val - 1) ?_ ?_ ?_
      · intro i hi; simp only [L0, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [Finset.mem_range]; omega
      · intro i1 h1 i2 h2 heq
        simp only [L0, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact Fin.ext (by omega)
      · intro t ht
        rw [Finset.mem_range] at ht
        refine ⟨⟨t + 1, by omega⟩, ?_, by dsimp only; omega⟩
        simp only [L0, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    let hits : Fin M → Finset (Fin n) → Prop := fun seed P =>
      ∃ t : Fin q,
        let w := ask seed (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed) t.val)
        w c0 = b0 ∧ L0.filter (fun ℓ => w ℓ = true) = P
    classical
    have hP_lb : ∀ P ∈ L0.powerset, Rej.card - fn ≤ (Rej.filter (fun seed => hits seed P)).card := by
      intro P hP
      have hPL0 : P ⊆ L0 := Finset.mem_powerset.1 hP
      let A := starF c0 b0 L0 (fun ℓ => decide (ℓ ∈ P))
      have hA_yes : M ≤ yes A + fn := hhigh A (hcount_star c0 b0 L0 _ hc0_L0 hL0_card)
      let YesA := (Finset.univ : Finset (Fin M)).filter (fun seed : Fin M =>
        report seed (PEqualNP.Outside.L_lib_679.runHist (sat A) (ask seed) q) = true)
      have hYesA_card : YesA.card = yes A := (hyes_hist A).symm
      let Miss := Rej.filter (fun seed => ¬ hits seed P)
      have hdisj : Disjoint Miss YesA := by
        rw [Finset.disjoint_left]
        intro seed h1 h2
        simp only [Miss, Finset.mem_filter] at h1
        simp only [YesA, Finset.mem_filter, Finset.mem_univ, true_and] at h2
        obtain ⟨t, hwc, hfilt⟩ := hhit_star L0 P seed h1.1 h2
        rw [Finset.inter_eq_left.2 hPL0] at hfilt
        exact h1.2 ⟨t, hwc, hfilt⟩
      have hMiss_le : Miss.card ≤ fn := by
        have hle : (Miss ∪ YesA).card ≤ M := by
          calc (Miss ∪ YesA).card
              ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_le_card (Finset.subset_univ _)
            _ = M := by rw [Finset.card_univ, Fintype.card_fin]
        rw [Finset.card_union_of_disjoint hdisj, hYesA_card] at hle
        omega
      dsimp only [Miss] at hMiss_le
      have hsplit := Finset.card_filter_add_card_filter_not (s := Rej) (fun seed => hits seed P)
      omega
    have hseed_ub : ∀ seed ∈ Rej, (L0.powerset.filter (fun P => hits seed P)).card ≤ q := by
      intro seed _
      let img := (Finset.univ : Finset (Fin q)).image (fun t : Fin q =>
        L0.filter (fun ℓ => (ask seed (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed) t.val)) ℓ = true))
      have hsub : L0.powerset.filter (fun P => hits seed P) ⊆ img := by
        intro P hP
        obtain ⟨t, _, rfl⟩ := (Finset.mem_filter.1 hP).2
        exact Finset.mem_image.2 ⟨t, Finset.mem_univ t, rfl⟩
      calc (L0.powerset.filter (fun P => hits seed P)).card
          ≤ img.card := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_image_le
        _ = q := by rw [Finset.card_univ, Fintype.card_fin]
    have hdouble :
        ∑ P ∈ L0.powerset, (Rej.filter (fun seed => hits seed P)).card =
        ∑ seed ∈ Rej, (L0.powerset.filter (fun P => hits seed P)).card := by
      have h1 : ∀ P, (Rej.filter (fun seed => hits seed P)).card =
          ∑ seed ∈ Rej, if hits seed P then 1 else 0 := fun P => by rw [Finset.sum_boole]; simp
      have h2 : ∀ seed, (L0.powerset.filter (fun P => hits seed P)).card =
          ∑ P ∈ L0.powerset, if hits seed P then 1 else 0 := fun seed => by rw [Finset.sum_boole]; simp
      simp_rw [h1, h2]
      exact Finset.sum_comm
    have hR_ineq : 2 ^ (s - 1) * (Rej.card - fn) ≤ q * Rej.card := by
      have hlb : 2 ^ (s - 1) * (Rej.card - fn) ≤
          ∑ P ∈ L0.powerset, (Rej.filter (fun seed => hits seed P)).card := by
        calc 2 ^ (s - 1) * (Rej.card - fn)
            = L0.powerset.card * (Rej.card - fn) := by rw [Finset.card_powerset, hL0_card]
          _ = ∑ _P ∈ L0.powerset, (Rej.card - fn) := by simp
          _ ≤ ∑ P ∈ L0.powerset, (Rej.filter (fun seed => hits seed P)).card :=
              Finset.sum_le_sum hP_lb
      have hub : ∑ seed ∈ Rej, (L0.powerset.filter (fun P => hits seed P)).card ≤ q * Rej.card := by
        calc ∑ seed ∈ Rej, (L0.powerset.filter (fun P => hits seed P)).card
            ≤ ∑ _seed ∈ Rej, q := Finset.sum_le_sum hseed_ub
          _ = Rej.card * q := by simp
          _ = q * Rej.card := Nat.mul_comm _ _
      omega
    have hstep1 : Rej.card * (M - fp - fn) ≤ (Rej.card - fn) * (M - fp) := by
      have hfn_le : fn * (M - fp) ≤ fn * Rej.card := Nat.mul_le_mul_left fn hRej_ge
      have h1 : Rej.card * (M - fp - fn) + Rej.card * fn = Rej.card * (M - fp) := by
        rw [← mul_add, Nat.sub_add_cancel (by omega)]
      have h2 : (Rej.card - fn) * (M - fp) + fn * (M - fp) = Rej.card * (M - fp) := by
        rw [← add_mul, Nat.sub_add_cancel (by omega)]
      have h3 : Rej.card * fn = fn * Rej.card := Nat.mul_comm _ _
      omega
    have hstep2 : Rej.card * (2 ^ (s - 1) * (M - fp - fn)) ≤ Rej.card * (q * (M - fp)) := by
      calc Rej.card * (2 ^ (s - 1) * (M - fp - fn))
          = 2 ^ (s - 1) * (Rej.card * (M - fp - fn)) := by ring
        _ ≤ 2 ^ (s - 1) * ((Rej.card - fn) * (M - fp)) := Nat.mul_le_mul_left _ hstep1
        _ = (2 ^ (s - 1) * (Rej.card - fn)) * (M - fp) := by ring
        _ ≤ (q * Rej.card) * (M - fp) := Nat.mul_le_mul_right _ hR_ineq
        _ = Rej.card * (q * (M - fp)) := by ring
    exact Nat.le_of_mul_le_mul_left hstep2 hRej_pos
  have hpart2 : fn = 0 → 2 ^ (s - 3) * Nat.clog 2 (2 * (n - s + 2) + 2) ≤ q := by
    intro hfn0
    obtain ⟨seed0, hseed0⟩ := Finset.card_pos.1 hRej_pos
    let wOf : Fin q → W := fun t =>
      ask seed0 (PEqualNP.Outside.L_lib_679.runHist (sat B) (ask seed0) t.val)
    let W0 : Finset (Fin q) := Finset.univ.filter (fun t : Fin q => wOf t c0 = b0)
    have hcover : ∀ (L : Finset (Fin n)) (σ : Fin n → Bool),
        c0 ∉ L → L.card = s - 1 →
        ∃ t ∈ W0, ∀ ℓ ∈ L, wOf t ℓ = σ ℓ := by
      intro L σ hcL hLcard
      let P : Finset (Fin n) := L.filter (fun ℓ => σ ℓ = true)
      have hσ_eq : ∀ ℓ ∈ L, decide (ℓ ∈ P) = σ ℓ := by
        intro ℓ hℓ; simp only [P, Finset.mem_filter, hℓ, true_and]; cases σ ℓ <;> simp
      let A := starF c0 b0 L (fun ℓ => decide (ℓ ∈ P))
      have hA_yes : M ≤ yes A := by
        have := hhigh A (hcount_star c0 b0 L _ hcL hLcard)
        omega
      have hseed0_acc : report seed0 (PEqualNP.Outside.L_lib_679.runHist (sat A) (ask seed0) q) = true := by
        by_contra hno
        have hnot : seed0 ∉ (Finset.univ : Finset (Fin M)).filter (fun seed : Fin M =>
            report seed (PEqualNP.Outside.L_lib_679.runHist (sat A) (ask seed) q) = true) := by
          simp [hno]
        have hlt : yes A < M := by
          rw [hyes_hist A]
          calc ((Finset.univ : Finset (Fin M)).filter (fun seed : Fin M =>
                report seed (PEqualNP.Outside.L_lib_679.runHist (sat A) (ask seed) q) = true)).card
              ≤ ((Finset.univ : Finset (Fin M)).erase seed0).card :=
                Finset.card_le_card (fun x hx => Finset.mem_erase.2 ⟨fun h => hnot (h ▸ hx), Finset.mem_univ x⟩)
            _ < (Finset.univ : Finset (Fin M)).card := Finset.card_erase_lt_of_mem (Finset.mem_univ seed0)
            _ = M := by rw [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨t, hwc, hfilt⟩ := hhit_star L P seed0 hseed0 hseed0_acc
      have hPL : P ⊆ L := Finset.filter_subset _ _
      rw [Finset.inter_eq_left.2 hPL] at hfilt
      refine ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ t, hwc⟩, fun ℓ hℓ => ?_⟩
      have hiff := Finset.ext_iff.1 hfilt ℓ
      simp only [Finset.mem_filter, hℓ, true_and, P] at hiff
      change wOf t ℓ = true ↔ σ ℓ = true at hiff
      cases hw : wOf t ℓ <;> cases hσ : σ ℓ <;> simp_all
    let S0 : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => 1 ≤ i.val ∧ i.val < s - 2)
    have hc0_S0 : c0 ∉ S0 := by simp [S0, c0]
    have hS0_card : S0.card = s - 3 := by
      rw [← Finset.card_range (s - 3)]
      refine Finset.card_bij (fun i _ => i.val - 1) ?_ ?_ ?_
      · intro i hi; simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [Finset.mem_range]; omega
      · intro i1 h1 i2 h2 heq
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact Fin.ext (by omega)
      · intro t ht
        rw [Finset.mem_range] at ht
        refine ⟨⟨t + 1, by omega⟩, ?_, by dsimp only; omega⟩
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    let Rem : Finset (Fin n) := Finset.univ \ insert c0 S0
    have hRem_card : Rem.card = n - s + 2 := by
      dsimp only [Rem]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem hc0_S0, hS0_card]
      omega
    let Slice : Finset (Fin n) → Finset (Fin q) := fun τ =>
      W0.filter (fun t => S0.filter (fun i => wOf t i = true) = τ)
    have hSlice_lb : ∀ τ ∈ S0.powerset, Nat.clog 2 (2 * (n - s + 2) + 2) ≤ (Slice τ).card := by
      intro τ hτ
      have hτS0 : τ ⊆ S0 := Finset.mem_powerset.1 hτ
      have hpair : ∀ (u1 u2 : Fin n) (a1 a2 : Bool),
          u1 ∈ Rem → u2 ∈ Rem → u1 ≠ u2 →
          ∃ t ∈ Slice τ, wOf t u1 = a1 ∧ wOf t u2 = a2 := by
        intro u1 u2 a1 a2 hu1 hu2 hne
        have hu1_not : u1 ∉ insert c0 S0 := (Finset.mem_sdiff.1 hu1).2
        have hu2_not : u2 ∉ insert c0 S0 := (Finset.mem_sdiff.1 hu2).2
        have hu1_c0 : u1 ≠ c0 := fun h => hu1_not (Finset.mem_insert.2 (Or.inl h))
        have hu2_c0 : u2 ≠ c0 := fun h => hu2_not (Finset.mem_insert.2 (Or.inl h))
        have hu1_S0 : u1 ∉ S0 := fun h => hu1_not (Finset.mem_insert.2 (Or.inr h))
        have hu2_S0 : u2 ∉ S0 := fun h => hu2_not (Finset.mem_insert.2 (Or.inr h))
        let L := insert u1 (insert u2 S0)
        have hcL : c0 ∉ L := by
          simp only [L, Finset.mem_insert, not_or]
          exact ⟨hu1_c0.symm, hu2_c0.symm, hc0_S0⟩
        have hLcard : L.card = s - 1 := by
          have hu1_ins : u1 ∉ insert u2 S0 := by
            simp only [Finset.mem_insert, not_or]; exact ⟨hne, hu1_S0⟩
          rw [Finset.card_insert_of_notMem hu1_ins, Finset.card_insert_of_notMem hu2_S0, hS0_card]
          omega
        let σ : Fin n → Bool := fun i => if i = u1 then a1 else if i = u2 then a2 else decide (i ∈ τ)
        obtain ⟨t, htW0, hall⟩ := hcover L σ hcL hLcard
        refine ⟨t, Finset.mem_filter.2 ⟨htW0, ?_⟩, ?_, ?_⟩
        · ext i
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hiS0, hwi⟩
            have h1 : i ≠ u1 := fun h => hu1_S0 (h ▸ hiS0)
            have h2 : i ≠ u2 := fun h => hu2_S0 (h ▸ hiS0)
            have hiL : i ∈ L := Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inr hiS0)))
            have h := hall i hiL
            simp only [σ, h1, h2, ite_false] at h
            rw [hwi] at h
            exact of_decide_eq_true h.symm
          · intro hiτ
            have hiS0 : i ∈ S0 := hτS0 hiτ
            have h1 : i ≠ u1 := fun h => hu1_S0 (h ▸ hiS0)
            have h2 : i ≠ u2 := fun h => hu2_S0 (h ▸ hiS0)
            have hiL : i ∈ L := Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2 (Or.inr hiS0)))
            have h := hall i hiL
            simp only [σ, h1, h2, ite_false, hiτ, decide_true] at h
            exact ⟨hiS0, h⟩
        · have h := hall u1 (Finset.mem_insert_self u1 _)
          simpa [σ] using h
        · have h := hall u2 (Finset.mem_insert.2 (Or.inr (Finset.mem_insert_self u2 _)))
          simpa [σ, hne.symm] using h
      have hRem_ne : Nonempty {i : Fin n // i ∈ Rem} := by
        obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < Rem.card)
        exact ⟨⟨u, hu⟩⟩
      have hpow := PEqualNP.Outside.L_lib_679.distinct_signed_columns
        (α := {i : Fin n // i ∈ Rem}) (β := {t : Fin q // t ∈ Slice τ})
        (fun t i => wOf t.1 i.1)
        (fun a => by
          have hother : 0 < (Rem.erase a.1).card := by
            rw [Finset.card_erase_of_mem a.2]; omega
          obtain ⟨v, hv⟩ := Finset.card_pos.1 hother
          have hv' := Finset.mem_erase.1 hv
          constructor
          · obtain ⟨t, ht, hta, _⟩ := hpair a.1 v true false a.2 hv'.2 hv'.1.symm
            exact ⟨⟨t, ht⟩, hta⟩
          · obtain ⟨t, ht, hta, _⟩ := hpair a.1 v false false a.2 hv'.2 hv'.1.symm
            exact ⟨⟨t, ht⟩, hta⟩)
        (fun a1 a2 hne => by
          have hval : a1.1 ≠ a2.1 := fun h => hne (Subtype.ext h)
          constructor
          · obtain ⟨t, ht, h1, h2⟩ := hpair a1.1 a2.1 true false a1.2 a2.2 hval
            exact ⟨⟨t, ht⟩, by rw [h1, h2]; decide⟩
          · obtain ⟨t, ht, h1, h2⟩ := hpair a1.1 a2.1 true true a1.2 a2.2 hval
            exact ⟨⟨t, ht⟩, by rw [h1, h2]⟩)
        hRem_ne
      simp only [Fintype.card_coe, hRem_card] at hpow
      exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 hpow
    have hdisj_slice : (S0.powerset : Set (Finset (Fin n))).PairwiseDisjoint Slice := by
      intro τ1 _ τ2 _ hne
      change Disjoint (Slice τ1) (Slice τ2)
      rw [Finset.disjoint_left]
      intro t h1 h2
      simp only [Slice, Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
    calc 2 ^ (s - 3) * Nat.clog 2 (2 * (n - s + 2) + 2)
        = S0.powerset.card * Nat.clog 2 (2 * (n - s + 2) + 2) := by rw [Finset.card_powerset, hS0_card]
      _ = ∑ _τ ∈ S0.powerset, Nat.clog 2 (2 * (n - s + 2) + 2) := by simp
      _ ≤ ∑ τ ∈ S0.powerset, (Slice τ).card := Finset.sum_le_sum hSlice_lb
      _ = (S0.powerset.biUnion Slice).card := (Finset.card_biUnion hdisj_slice).symm
      _ ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = q := by rw [Finset.card_univ, Fintype.card_fin]
  have hpart3 : fp = 0 → 2 * n + 2 ≤ 2 ^ q := by
    intro hfp0
    have hsat_empty : ∀ u : W, sat (∅ : F) u = true := fun u =>
      (hsat_iff ∅ u).2 (fun c hc => False.elim (Finset.notMem_empty c hc))
    have hcount_empty : count (∅ : F) = Q := by
      dsimp only [count, Q]
      have hall : (Finset.univ : Finset W).filter (fun u => sat (∅ : F) u = true) = Finset.univ := by
        ext u; simp [hsat_empty]
      rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have hhigh_empty : M ≤ yes (∅ : F) + fn := by
      apply hhigh (∅ : F)
      rw [hcount_empty, Nat.mul_comm (2 ^ s) Q]
      apply Nat.mul_le_mul_left Q
      have hpow : 2 ^ s = 2 ^ (s - 1) + 2 ^ (s - 1) := by
        conv_lhs => rw [show s = (s - 1) + 1 by omega, pow_succ, mul_two]
      have hpos : 1 ≤ 2 ^ (s - 1) := Nat.one_le_two_pow
      omega
    have hyes_empty_pos : 0 < yes (∅ : F) := by omega
    rw [hyes_hist (∅ : F)] at hyes_empty_pos
    obtain ⟨seed1, hseed1⟩ := Finset.card_pos.1 hyes_empty_pos
    have hseed1_acc : report seed1 (PEqualNP.Outside.L_lib_679.runHist (sat (∅ : F)) (ask seed1) q) = true :=
      (Finset.mem_filter.1 hseed1).2
    let w1 : Fin q → W := fun t =>
      ask seed1 (PEqualNP.Outside.L_lib_679.runHist (sat (∅ : F)) (ask seed1) t.val)
    have hfalsify : ∀ A : F, 2 * count A ≤ Q → ∃ t : Fin q, sat A (w1 t) = false := by
      intro A hA
      have hyes0 : yes A = 0 := by
        have := hlow A hA
        omega
      rw [hyes_hist A] at hyes0
      have hseed1_rej : report seed1 (PEqualNP.Outside.L_lib_679.runHist (sat A) (ask seed1) q) = false := by
        cases h : report seed1 (PEqualNP.Outside.L_lib_679.runHist (sat A) (ask seed1) q)
        · rfl
        · exfalso
          have hmem : seed1 ∈ (Finset.univ : Finset (Fin M)).filter (fun seed : Fin M =>
              report seed (PEqualNP.Outside.L_lib_679.runHist (sat A) (ask seed) q) = true) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ seed1, h⟩
          have hpos := Finset.card_pos.2 ⟨seed1, hmem⟩
          omega
      by_contra hno
      push Not at hno
      have hagree : ∀ t < q,
          sat A (ask seed1 (PEqualNP.Outside.L_lib_679.runHist (sat (∅ : F)) (ask seed1) t)) =
          sat (∅ : F) (ask seed1 (PEqualNP.Outside.L_lib_679.runHist (sat (∅ : F)) (ask seed1) t)) := by
        intro t ht
        have hnt := hno ⟨t, ht⟩
        have hAt : sat A (w1 ⟨t, ht⟩) = true := by
          cases h : sat A (w1 ⟨t, ht⟩)
          · exact absurd h hnt
          · rfl
        exact hAt.trans (hsat_empty _).symm
      have heq := PEqualNP.Outside.L_lib_679.runHist_eq_of_sat_eq (sat A) (sat (∅ : F)) (ask seed1) q hagree
      rw [heq, hseed1_acc] at hseed1_rej
      exact Bool.false_ne_true hseed1_rej.symm
    have hpow := PEqualNP.Outside.L_lib_679.distinct_signed_columns
      (α := Fin n) (β := Fin q) w1
      (fun a => by
        constructor
        · obtain ⟨t, ht⟩ := hfalsify (baseF a true) (by rw [hcount_base])
          refine ⟨t, ?_⟩
          by_contra hnt
          have htrue : sat (baseF a true) (w1 t) = true := (hsat_base a true (w1 t)).2 hnt
          rw [htrue] at ht; exact Bool.false_ne_true ht.symm
        · obtain ⟨t, ht⟩ := hfalsify (baseF a false) (by rw [hcount_base])
          refine ⟨t, ?_⟩
          by_contra hnt
          have htrue : sat (baseF a false) (w1 t) = true := (hsat_base a false (w1 t)).2 hnt
          rw [htrue] at ht; exact Bool.false_ne_true ht.symm)
      (fun a1 a2 hne => by
        let Aeq : F := {((a1, true), (a2, false)), ((a1, false), (a2, true))}
        have hsat_eq : ∀ w : W, sat Aeq w = true ↔ w a1 = w a2 := by
          intro w
          rw [hsat_iff]
          constructor
          · intro hall
            have h1 := hall ((a1, true), (a2, false)) (Finset.mem_insert_self _ _)
            have h2 := hall ((a1, false), (a2, true)) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            cases hw1 : w a1 <;> cases hw2 : w a2
            · rfl
            · rw [hw1, hw2] at h2; simp at h2
            · rw [hw1, hw2] at h1; simp at h1
            · rfl
          · intro heq c hc
            rcases Finset.mem_insert.1 hc with rfl | hc2
            · dsimp only; rw [heq]; cases w a2 <;> simp
            · rw [Finset.mem_singleton.1 hc2]; dsimp only; rw [heq]; cases w a2 <;> simp
        have hcnt_eq : 2 * count Aeq = Q := by
          dsimp only [count, Q]
          have hfilt : (Finset.univ : Finset W).filter (fun u => sat Aeq u = true) =
              (Finset.univ : Finset W).filter (fun u => u a1 = u a2) := by
            ext u; simp [hsat_eq]
          rw [hfilt]
          refine PEqualNP.Outside.L_lib_679.card_filter_eq_half (fun u => u a1 = u a2) a1 (fun w => ?_)
          simp only [PEqualNP.Outside.L_lib_679.flipAt, ite_true, hne.symm, ite_false]
          cases w a1 <;> cases w a2 <;> simp
        let Ane : F := {((a1, true), (a2, true)), ((a1, false), (a2, false))}
        have hsat_ne : ∀ w : W, sat Ane w = true ↔ w a1 ≠ w a2 := by
          intro w
          rw [hsat_iff]
          constructor
          · intro hall
            have h1 := hall ((a1, true), (a2, true)) (Finset.mem_insert_self _ _)
            have h2 := hall ((a1, false), (a2, false)) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
            cases hw1 : w a1 <;> cases hw2 : w a2
            · rw [hw1, hw2] at h2; simp at h2
            · decide
            · decide
            · rw [hw1, hw2] at h1; simp at h1
          · intro hneq c hc
            rcases Finset.mem_insert.1 hc with rfl | hc2
            · dsimp only
              cases hw1 : w a1 <;> cases hw2 : w a2
              · left; simp
              · left; simp
              · right; simp
              · rw [hw1, hw2] at hneq; exact absurd rfl hneq
            · rw [Finset.mem_singleton.1 hc2]; dsimp only
              cases hw1 : w a1 <;> cases hw2 : w a2
              · rw [hw1, hw2] at hneq; exact absurd rfl hneq
              · right; simp
              · left; simp
              · left; simp
        have hcnt_ne : 2 * count Ane = Q := by
          dsimp only [count, Q]
          have hfilt : (Finset.univ : Finset W).filter (fun u => sat Ane u = true) =
              (Finset.univ : Finset W).filter (fun u => u a1 ≠ u a2) := by
            ext u; simp [hsat_ne]
          rw [hfilt]
          refine PEqualNP.Outside.L_lib_679.card_filter_eq_half (fun u => u a1 ≠ u a2) a1 (fun w => ?_)
          simp only [PEqualNP.Outside.L_lib_679.flipAt, ite_true, hne.symm, ite_false]
          cases w a1 <;> cases w a2 <;> simp
        constructor
        · obtain ⟨t, ht⟩ := hfalsify Aeq (by rw [hcnt_eq])
          refine ⟨t, ?_⟩
          intro heq
          have htrue : sat Aeq (w1 t) = true := (hsat_eq (w1 t)).2 heq
          rw [htrue] at ht; exact Bool.false_ne_true ht.symm
        · obtain ⟨t, ht⟩ := hfalsify Ane (by rw [hcnt_ne])
          refine ⟨t, ?_⟩
          by_contra hneq
          have htrue : sat Ane (w1 t) = true := (hsat_ne (w1 t)).2 hneq
          rw [htrue] at ht; exact Bool.false_ne_true ht.symm)
      ⟨c0⟩
    simp only [Fintype.card_fin] at hpow
    exact hpow
  exact ⟨hpart1, hpart2, hpart3⟩
