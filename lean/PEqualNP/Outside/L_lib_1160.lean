import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1160

private abbrev Site (d : Nat) := Fin (d + 2)
private abbrev Bits (d : Nat) := Finset (Site d)
private abbrev Signing (d : Nat) := Site d → Bool × Bool

private def extraSet (d : Nat) : Bits d :=
  (Finset.univ : Bits d) \ ({0, 1} : Bits d)

private noncomputable def liveFn (d : Nat) (on : Bool) (w x : Bits d) : Bool :=
  let a := decide ((0 : Site d) ∈ x)
  let b := decide ((1 : Site d) ∈ x)
  !(a && b) && (if on then !(a && b) else a || b) &&
    (extraSet d).toList.all (fun j => a || b || (decide (j ∈ x) == decide (j ∈ w)))

private def passes (d : Nat) (f : Signing d) (x : Bits d) : Prop :=
  ∀ i : Site d, (decide (i ∈ x), decide ((i + 1 : Site d) ∈ x)) ≠ f i

private noncomputable def replyFn (d : Nat) (on : Bool) (w : Bits d) (f : Signing d) : Bool :=
  (Finset.univ : Finset (Bits d)).toList.any (fun x =>
    liveFn d on w x && (Finset.univ : Bits d).toList.all (fun i =>
      (decide (i ∈ x), decide ((i + 1 : Site d) ∈ x)) != f i))

private def baseX (d : Nat) (w : Bits d) : Bits d :=
  w ∩ extraSet d

private lemma zero_ne_one_site (d : Nat) : (0 : Site d) ≠ (1 : Site d) := by
  intro h
  have hval := congrArg Fin.val h
  change 0 = 1 % (d + 2) at hval
  have hlt : 1 < d + 2 := by omega
  rw [Nat.mod_eq_of_lt hlt] at hval
  omega

private lemma mem_extraSet {d : Nat} (j : Site d) :
    j ∈ extraSet d ↔ j ≠ 0 ∧ j ≠ 1 := by
  simp [extraSet]

private lemma zero_not_mem_baseX {d : Nat} (w : Bits d) : (0 : Site d) ∉ baseX d w := by
  simp [baseX, extraSet]

private lemma one_not_mem_baseX {d : Nat} (w : Bits d) : (1 : Site d) ∉ baseX d w := by
  simp [baseX, extraSet]

private lemma baseX_subset_extra {d : Nat} (w : Bits d) : baseX d w ⊆ extraSet d :=
  Finset.inter_subset_right

private lemma baseX_of_subset {d : Nat} {w : Bits d} (hw : w ⊆ extraSet d) :
    baseX d w = w :=
  Finset.inter_eq_left.mpr hw

private lemma liveFn_false_iff {d : Nat} (w x : Bits d) :
    liveFn d false w x = true ↔ decide ((0 : Site d) ∈ x) ≠ decide ((1 : Site d) ∈ x) := by
  unfold liveFn
  dsimp only
  cases h0 : decide ((0 : Site d) ∈ x) <;> cases h1 : decide ((1 : Site d) ∈ x) <;> simp

private lemma liveFn_true_iff {d : Nat} (w x : Bits d) :
    liveFn d true w x = true ↔
      decide ((0 : Site d) ∈ x) ≠ decide ((1 : Site d) ∈ x) ∨ x = baseX d w := by
  unfold liveFn
  dsimp only
  cases h0 : decide ((0 : Site d) ∈ x) <;> cases h1 : decide ((1 : Site d) ∈ x)
  · simp only [Bool.false_and, Bool.not_false, ↓reduceIte, Bool.true_and, Bool.false_or,
      List.all_eq_true, Finset.mem_toList, beq_iff_eq, ne_eq, not_true_eq_false, false_or]
    constructor
    · intro hall
      ext j
      by_cases hj0 : j = 0
      · subst hj0
        have hx0 : (0 : Site d) ∉ x := of_decide_eq_false h0
        simp [hx0, zero_not_mem_baseX]
      · by_cases hj1 : j = 1
        · subst hj1
          have hx1 : (1 : Site d) ∉ x := of_decide_eq_false h1
          simp [hx1, one_not_mem_baseX]
        · have hjE : j ∈ extraSet d := (mem_extraSet j).mpr ⟨hj0, hj1⟩
          have hdec := hall j hjE
          simp only [baseX, Finset.mem_inter, hjE, and_true]
          exact decide_eq_decide.mp hdec
    · intro hxeq j hjE
      subst hxeq
      simp only [baseX, Finset.mem_inter, hjE, and_true]
  · simp
  · simp
  · simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true, ne_eq,
      not_true_eq_false, false_or, false_iff]
    intro hxeq
    have hx0 : (0 : Site d) ∈ x := of_decide_eq_true h0
    rw [hxeq] at hx0
    exact zero_not_mem_baseX w hx0

private lemma replyFn_iff {d : Nat} (on : Bool) (w : Bits d) (f : Signing d) :
    replyFn d on w f = true ↔ ∃ x : Bits d, liveFn d on w x = true ∧ passes d f x := by
  unfold replyFn passes
  simp only [List.any_eq_true, Finset.mem_toList, Finset.mem_univ, true_and, true_implies,
    Bool.and_eq_true, List.all_eq_true, bne_iff_ne]

private lemma replyFn_false_indep {d : Nat} (w₁ w₂ : Bits d) (f : Signing d) :
    replyFn d false w₁ f = replyFn d false w₂ f := by
  apply Bool.eq_iff_iff.mpr
  simp only [replyFn_iff, liveFn_false_iff]

private lemma replyFn_true_of_false {d : Nat} (w : Bits d) (f : Signing d)
    (h : replyFn d false ∅ f = true) : replyFn d true w f = true := by
  rw [replyFn_iff] at h ⊢
  rcases h with ⟨x, hlx, hpx⟩
  rw [liveFn_false_iff] at hlx
  exact ⟨x, (liveFn_true_iff w x).mpr (Or.inl hlx), hpx⟩

private def pathV (d : Nat) (t : Nat) : Site d :=
  ⟨(t + 1) % (d + 2), Nat.mod_lt _ (by omega)⟩

private lemma pathV_zero (d : Nat) : pathV d 0 = (1 : Site d) := by
  apply Fin.ext
  change (0 + 1) % (d + 2) = 1 % (d + 2)
  rfl

private lemma pathV_last (d : Nat) : pathV d (d + 1) = (0 : Site d) := by
  apply Fin.ext
  change (d + 1 + 1) % (d + 2) = 0
  have h : d + 1 + 1 = d + 2 := by omega
  rw [h, Nat.mod_self]

private lemma pathV_succ (d : Nat) (t : Nat) : pathV d (t + 1) = pathV d t + 1 := by
  apply Fin.ext
  change (t + 1 + 1) % (d + 2) = ((t + 1) % (d + 2) + 1 % (d + 2)) % (d + 2)
  rw [← Nat.add_mod]

private lemma pathV_val {d t : Nat} (ht : t < d + 1) : (pathV d t).val = t + 1 := by
  change (t + 1) % (d + 2) = t + 1
  exact Nat.mod_eq_of_lt (by omega)

private lemma pathV_ne_zero {d t : Nat} (ht : t < d + 1) : pathV d t ≠ (0 : Site d) := by
  intro h
  have hv := congrArg Fin.val h
  rw [pathV_val ht] at hv
  change t + 1 = 0 at hv
  omega

private lemma pathV_inj {d t₁ t₂ : Nat} (h1 : t₁ ≤ d + 1) (h2 : t₂ ≤ d + 1)
    (heq : pathV d t₁ = pathV d t₂) : t₁ = t₂ := by
  by_cases ht1 : t₁ = d + 1
  · subst ht1
    by_cases ht2 : t₂ = d + 1
    · exact ht2.symm
    · exfalso
      rw [pathV_last] at heq
      exact pathV_ne_zero (by omega) heq.symm
  · by_cases ht2 : t₂ = d + 1
    · subst ht2
      exfalso
      rw [pathV_last] at heq
      exact pathV_ne_zero (by omega) heq
    · have hv := congrArg Fin.val heq
      rw [pathV_val (by omega), pathV_val (by omega)] at hv
      omega

private lemma exists_pathV {d : Nat} (i : Site d) : ∃ t ≤ d + 1, pathV d t = i := by
  by_cases hi : i.val = 0
  · refine ⟨d + 1, le_refl _, ?_⟩
    rw [pathV_last]
    exact Fin.ext hi.symm
  · refine ⟨i.val - 1, by omega, ?_⟩
    apply Fin.ext
    rw [pathV_val (by omega)]
    omega

private def chainR (d : Nat) (f : Signing d) (b₀ : Bool) : Nat → Bool
  | 0 => b₀
  | t + 1 => !(f (pathV d t)).2

private lemma path_chain {d : Nat} (f : Signing d) (b₀ : Bool)
    (hkill : ∀ x : Bits d,
      decide ((1 : Site d) ∈ x) = b₀ →
      decide ((0 : Site d) ∈ x) = !b₀ →
      ∃ t < d + 1, (decide (pathV d t ∈ x), decide (pathV d (t + 1) ∈ x)) = f (pathV d t)) :
    ∃ r : Nat → Bool, r 0 = b₀ ∧ r (d + 1) = b₀ ∧
      ∀ t < d + 1, f (pathV d t) = (r t, !(r (t + 1))) := by
  let r : Nat → Bool := chainR d f b₀
  have hbuild : ∀ val : Nat → Bool,
      val 0 = b₀ → val (d + 1) = !b₀ →
      (∀ s < d + 1, (val s, val (s + 1)) ≠ f (pathV d s)) → False := by
    intro val hv0 hvl hok
    let x : Bits d := Finset.univ.filter (fun i =>
      val (if i.val = 0 then d + 1 else i.val - 1) = true)
    have hx_eval : ∀ t ≤ d + 1, decide (pathV d t ∈ x) = val t := by
      intro t ht
      have hidx : (if (pathV d t).val = 0 then d + 1 else (pathV d t).val - 1) = t := by
        by_cases hlast : t = d + 1
        · subst hlast; rw [pathV_last]; simp
        · rw [pathV_val (by omega)]
          have hne : t + 1 ≠ 0 := by omega
          simp [hne]
      have hmem : pathV d t ∈ x ↔ val t = true := by
        simp only [x, Finset.mem_filter, Finset.mem_univ, true_and, hidx]
      cases hvt : val t
      · exact decide_eq_false (by rw [hmem, hvt]; decide)
      · exact decide_eq_true (by rw [hmem, hvt])
    have hx1 : decide ((1 : Site d) ∈ x) = b₀ := by
      rw [← pathV_zero d, hx_eval 0 (Nat.zero_le _), hv0]
    have hx0 : decide ((0 : Site d) ∈ x) = !b₀ := by
      rw [← pathV_last d, hx_eval (d + 1) (le_refl _), hvl]
    rcases hkill x hx1 hx0 with ⟨s, hs, hbad⟩
    rw [hx_eval s (by omega), hx_eval (s + 1) (by omega)] at hbad
    exact hok s hs hbad
  have hfst : ∀ t < d + 1, (f (pathV d t)).1 = r t := by
    intro t₀ ht₀
    by_contra hne
    let val : Nat → Bool := fun t =>
      if t ≤ t₀ then r t
      else if t = d + 1 then !b₀
      else !(f (pathV d t)).1
    refine hbuild val ?_ ?_ ?_
    · simp [val, r, chainR]
    · have hnt : ¬ (d + 1 ≤ t₀) := by omega
      simp [val, hnt]
    · intro s hs
      by_cases hlt : s < t₀
      · have hs1 : s + 1 ≤ t₀ := by omega
        have hvs1 : val (s + 1) = !(f (pathV d s)).2 := by
          simp [val, hs1, r, chainR]
        intro heq
        have h2 := congrArg Prod.snd heq
        rw [hvs1] at h2
        cases h : (f (pathV d s)).2 <;> simp [h] at h2
      · by_cases heqt : s = t₀
        · subst heqt
          have hvs : val s = r s := by simp [val]
          intro heq
          have h1 := congrArg Prod.fst heq
          rw [hvs] at h1
          exact hne h1.symm
        · have hnotle : ¬ (s ≤ t₀) := by omega
          have hnotl : s ≠ d + 1 := by omega
          have hvs : val s = !(f (pathV d s)).1 := by simp [val, hnotle, hnotl]
          intro heq
          have h1 := congrArg Prod.fst heq
          rw [hvs] at h1
          cases h : (f (pathV d s)).1 <;> simp [h] at h1
  have hlast : r (d + 1) = b₀ := by
    by_contra hne
    have hneg : r (d + 1) = !b₀ := by
      cases hb : b₀ <;> cases hr : r (d + 1) <;> simp [hb, hr] at hne ⊢
    refine hbuild r rfl hneg ?_
    intro s hs heq
    have h2 := congrArg Prod.snd heq
    change (!(f (pathV d s)).2) = (f (pathV d s)).2 at h2
    cases h : (f (pathV d s)).2 <;> simp [h] at h2
  refine ⟨r, rfl, hlast, ?_⟩
  intro t ht
  apply Prod.ext
  · exact hfst t ht
  · change (f (pathV d t)).2 = !(!(f (pathV d t)).2)
    simp

private lemma at_most_one_target {d : Nat} (f : Signing d)
    (h0 : replyFn d false ∅ f = false)
    {w₁ w₂ : Bits d}
    (hw1 : w₁ ⊆ extraSet d) (hw2 : w₂ ⊆ extraSet d)
    (hp1 : passes d f w₁) (hp2 : passes d f w₂) : w₁ = w₂ := by
  have hkill_all : ∀ x : Bits d,
      decide ((0 : Site d) ∈ x) ≠ decide ((1 : Site d) ∈ x) → ¬ passes d f x := by
    intro x hne hp
    have ht : replyFn d false ∅ f = true :=
      (replyFn_iff false ∅ f).mpr ⟨x, (liveFn_false_iff ∅ x).mpr hne, hp⟩
    rw [h0] at ht
    exact Bool.false_ne_true ht
  by_cases hf0 : f 0 = (false, true)
  · have hchain : ∀ x : Bits d,
        decide ((1 : Site d) ∈ x) = false →
        decide ((0 : Site d) ∈ x) = !false →
        ∃ t < d + 1, (decide (pathV d t ∈ x), decide (pathV d (t + 1) ∈ x)) = f (pathV d t) := by
      intro x hx1 hx0
      by_contra hall
      push_neg at hall
      have hpx : passes d f x := by
        intro i
        by_cases hi0 : i = 0
        · subst hi0
          simp only [zero_add, hx0, hx1, hf0, Bool.not_false]
          decide
        · rcases exists_pathV i with ⟨t, ht, rfl⟩
          have htlt : t < d + 1 := by
            by_contra hge
            have hteq : t = d + 1 := by omega
            subst hteq
            exact hi0 (pathV_last d)
          rw [← pathV_succ]
          exact hall t htlt
      have hne : decide ((0 : Site d) ∈ x) ≠ decide ((1 : Site d) ∈ x) := by
        rw [hx0, hx1]; decide
      exact hkill_all x hne hpx
    rcases path_chain f false hchain with ⟨r, hr0, _, hf_eq⟩
    have hdet : ∀ x : Bits d, (1 : Site d) ∉ x → passes d f x →
        ∀ t ≤ d + 1, decide (pathV d t ∈ x) = r t := by
      intro x hx1 hpx t
      induction t with
      | zero =>
        intro _
        rw [pathV_zero, hr0]
        exact decide_eq_false hx1
      | succ t ih =>
        intro hts
        have hprev := ih (by omega)
        have hedge := hpx (pathV d t)
        rw [← pathV_succ, hf_eq t (by omega), hprev] at hedge
        cases hcur : decide (pathV d (t + 1) ∈ x) <;> cases hrt : r (t + 1) <;>
          simp [hcur, hrt] at hedge ⊢
    have h1w1 : (1 : Site d) ∉ w₁ := fun h => ((mem_extraSet 1).mp (hw1 h)).2 rfl
    have h1w2 : (1 : Site d) ∉ w₂ := fun h => ((mem_extraSet 1).mp (hw2 h)).2 rfl
    ext i
    rcases exists_pathV i with ⟨t, ht, rfl⟩
    have h1 := hdet w₁ h1w1 hp1 t ht
    have h2 := hdet w₂ h1w2 hp2 t ht
    exact decide_eq_decide.mp (h1.trans h2.symm)
  · have hchain : ∀ x : Bits d,
        decide ((1 : Site d) ∈ x) = true →
        decide ((0 : Site d) ∈ x) = !true →
        ∃ t < d + 1, (decide (pathV d t ∈ x), decide (pathV d (t + 1) ∈ x)) = f (pathV d t) := by
      intro x hx1 hx0
      by_contra hall
      push_neg at hall
      have hpx : passes d f x := by
        intro i
        by_cases hi0 : i = 0
        · subst hi0
          simp only [zero_add, hx0, hx1, Bool.not_true]
          exact Ne.symm hf0
        · rcases exists_pathV i with ⟨t, ht, rfl⟩
          have htlt : t < d + 1 := by
            by_contra hge
            have hteq : t = d + 1 := by omega
            subst hteq
            exact hi0 (pathV_last d)
          rw [← pathV_succ]
          exact hall t htlt
      have hne : decide ((0 : Site d) ∈ x) ≠ decide ((1 : Site d) ∈ x) := by
        rw [hx0, hx1]; decide
      exact hkill_all x hne hpx
    rcases path_chain f true hchain with ⟨r, _, hrlast, hf_eq⟩
    have hdet : ∀ x : Bits d, (0 : Site d) ∉ x → passes d f x →
        ∀ k ≤ d + 1, decide (pathV d (d + 1 - k) ∈ x) = !(r (d + 1 - k)) := by
      intro x hx0 hpx k
      induction k with
      | zero =>
        intro _
        simp only [Nat.sub_zero, pathV_last, hrlast, Bool.not_true]
        exact decide_eq_false hx0
      | succ k ih =>
        intro hks
        have hprev := ih (by omega)
        set t := d + 1 - (k + 1) with ht_def
        have htlt : t < d + 1 := by omega
        have ht1 : t + 1 = d + 1 - k := by omega
        have hedge := hpx (pathV d t)
        rw [← pathV_succ, ht1, hf_eq t htlt, ht1, hprev] at hedge
        cases hcur : decide (pathV d t ∈ x) <;> cases hrt : r t <;>
          simp [hcur, hrt] at hedge ⊢
    have h0w1 : (0 : Site d) ∉ w₁ := fun h => ((mem_extraSet 0).mp (hw1 h)).1 rfl
    have h0w2 : (0 : Site d) ∉ w₂ := fun h => ((mem_extraSet 0).mp (hw2 h)).1 rfl
    ext i
    rcases exists_pathV i with ⟨t, ht, rfl⟩
    have h1 := hdet w₁ h0w1 hp1 (d + 1 - t) (by omega)
    have h2 := hdet w₂ h0w2 hp2 (d + 1 - t) (by omega)
    have hsub : d + 1 - (d + 1 - t) = t := by omega
    rw [hsub] at h1 h2
    exact decide_eq_decide.mp (h1.trans h2.symm)

private def pointSigning (d : Nat) (w₀ : Bits d) : Signing d :=
  fun i => if i = 0 then (false, true)
    else (decide (i ∈ w₀), !(decide ((i + 1 : Site d) ∈ w₀)))

private lemma pointSigning_passes_iff {d : Nat} {w₀ : Bits d} (hw₀ : w₀ ⊆ extraSet d)
    {x : Bits d} (hx1 : (1 : Site d) ∉ x) :
    passes d (pointSigning d w₀) x ↔ x = w₀ := by
  have hw0_0 : (0 : Site d) ∉ w₀ := fun h => ((mem_extraSet 0).mp (hw₀ h)).1 rfl
  have hw0_1 : (1 : Site d) ∉ w₀ := fun h => ((mem_extraSet 1).mp (hw₀ h)).2 rfl
  constructor
  · intro hpx
    have hagree : ∀ t ≤ d + 1, decide (pathV d t ∈ x) = decide (pathV d t ∈ w₀) := by
      intro t
      induction t with
      | zero =>
        intro _
        rw [pathV_zero, decide_eq_false hx1, decide_eq_false hw0_1]
      | succ t ih =>
        intro hts
        have hprev := ih (by omega)
        have hne0 : pathV d t ≠ 0 := pathV_ne_zero (by omega)
        have hedge := hpx (pathV d t)
        simp only [pointSigning, hne0, ↓reduceIte, ← pathV_succ, hprev] at hedge
        cases h1 : decide (pathV d (t + 1) ∈ x) <;> cases h2 : decide (pathV d (t + 1) ∈ w₀) <;>
          simp [h1, h2] at hedge ⊢
    ext i
    rcases exists_pathV i with ⟨t, ht, rfl⟩
    exact decide_eq_decide.mp (hagree t ht)
  · rintro rfl
    intro i
    by_cases hi0 : i = 0
    · subst hi0
      simp only [pointSigning, ↓reduceIte, zero_add, decide_eq_false hw0_0, decide_eq_false hw0_1]
      decide
    · simp only [pointSigning, hi0, ↓reduceIte]
      intro heq
      have h2 := congrArg Prod.snd heq
      cases h : decide ((i + 1 : Site d) ∈ x) <;> simp [h] at h2

private lemma replyFn_pointSigning_false {d : Nat} {w₀ : Bits d} (hw₀ : w₀ ⊆ extraSet d)
    (w : Bits d) : replyFn d false w (pointSigning d w₀) = false := by
  have hw0_0 : (0 : Site d) ∉ w₀ := fun h => ((mem_extraSet 0).mp (hw₀ h)).1 rfl
  apply Bool.eq_false_iff.mpr
  intro ht
  rcases (replyFn_iff false w (pointSigning d w₀)).mp ht with ⟨x, hlx, hpx⟩
  rw [liveFn_false_iff] at hlx
  by_cases hx1 : (1 : Site d) ∈ x
  · have hx0 : (0 : Site d) ∉ x := by
      intro h0
      exact hlx (by rw [decide_eq_true h0, decide_eq_true hx1])
    have hedge := hpx 0
    simp only [pointSigning, ↓reduceIte, zero_add, decide_eq_false hx0, decide_eq_true hx1] at hedge
    exact hedge rfl
  · have hx0 : (0 : Site d) ∈ x := by
      by_contra h0
      exact hlx (by rw [decide_eq_false h0, decide_eq_false hx1])
    have hxeq := (pointSigning_passes_iff hw₀ hx1).mp hpx
    subst hxeq
    exact hw0_0 hx0

private lemma replyFn_pointSigning_true {d : Nat} {w₀ : Bits d} (hw₀ : w₀ ⊆ extraSet d)
    (w : Bits d) : replyFn d true w (pointSigning d w₀) = decide (baseX d w = w₀) := by
  apply Bool.eq_iff_iff.mpr
  rw [replyFn_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨x, hlx, hpx⟩
    rcases (liveFn_true_iff w x).mp hlx with hne | rfl
    · exfalso
      have ht : replyFn d false w (pointSigning d w₀) = true :=
        (replyFn_iff false w (pointSigning d w₀)).mpr ⟨x, (liveFn_false_iff w x).mpr hne, hpx⟩
      rw [replyFn_pointSigning_false hw₀ w] at ht
      exact Bool.false_ne_true ht
    · exact (pointSigning_passes_iff hw₀ (one_not_mem_baseX w)).mp hpx
  · intro hbe
    refine ⟨baseX d w, (liveFn_true_iff w (baseX d w)).mpr (Or.inr rfl), ?_⟩
    exact (pointSigning_passes_iff hw₀ (one_not_mem_baseX w)).mpr hbe

private lemma card_extraSet (d : Nat) : (extraSet d).card = d := by
  have hsub : ({0, 1} : Bits d) ⊆ (Finset.univ : Bits d) := Finset.subset_univ _
  have hcard : (extraSet d).card = (Finset.univ : Bits d).card - ({0, 1} : Bits d).card := by
    unfold extraSet
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  rw [hcard, Finset.card_univ, Fintype.card_fin, Finset.card_pair (zero_ne_one_site d)]
  omega

private lemma card_extraSet_powerset (d : Nat) : (extraSet d).powerset.card = 2 ^ d := by
  rw [Finset.card_powerset, card_extraSet]

private noncomputable def runPrefix {d k : Nat} (ask : Fin k → List Bool → Signing d)
    (on : Bool) (w : Bits d) (m : Nat) : List Bool :=
  ((List.finRange k).take m).foldl (fun h j => h ++ [replyFn d on w (ask j h)]) []

private lemma runPrefix_succ {d k : Nat} (ask : Fin k → List Bool → Signing d)
    (on : Bool) (w : Bits d) {m : Nat} (hm : m < k) :
    runPrefix ask on w (m + 1) =
      runPrefix ask on w m ++
        [replyFn d on w (ask ⟨m, hm⟩ (runPrefix ask on w m))] := by
  unfold runPrefix
  have hlen : m < (List.finRange k).length := by simp [hm]
  rw [List.take_succ_eq_append_getElem hlen, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp

private lemma card_diff_le {d k : Nat} (ask : Fin k → List Bool → Signing d) :
    ∀ m ≤ k,
      ((extraSet d).powerset.filter (fun w =>
        runPrefix ask true w m ≠ runPrefix ask false ∅ m)).card ≤ m := by
  intro m
  induction m with
  | zero =>
    intro _
    have hemp : (extraSet d).powerset.filter (fun w =>
        runPrefix ask true w 0 ≠ runPrefix ask false ∅ 0) = ∅ := by
      ext w
      simp [runPrefix]
    rw [hemp]; simp
  | succ m ih =>
    intro hmk
    have hm : m < k := by omega
    let prev := (extraSet d).powerset.filter (fun w =>
      runPrefix ask true w m ≠ runPrefix ask false ∅ m)
    let f : Signing d := ask ⟨m, hm⟩ (runPrefix ask false ∅ m)
    let fresh := (extraSet d).powerset.filter (fun w =>
      replyFn d true w f ≠ replyFn d false ∅ f)
    have hsub : (extraSet d).powerset.filter (fun w =>
        runPrefix ask true w (m + 1) ≠ runPrefix ask false ∅ (m + 1)) ⊆ prev ∪ fresh := by
      intro w hw
      simp only [Finset.mem_filter] at hw
      rw [Finset.mem_union]
      by_cases hp : runPrefix ask true w m ≠ runPrefix ask false ∅ m
      · exact Or.inl (Finset.mem_filter.mpr ⟨hw.1, hp⟩)
      · push_neg at hp
        refine Or.inr (Finset.mem_filter.mpr ⟨hw.1, ?_⟩)
        intro hrep
        apply hw.2
        rw [runPrefix_succ ask true w hm, runPrefix_succ ask false ∅ hm, hp]
        exact congrArg (fun b => runPrefix ask false ∅ m ++ [b]) hrep
    have hfresh_le : fresh.card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro w₁ hw1 w₂ hw2
      simp only [fresh, Finset.mem_filter, Finset.mem_powerset] at hw1 hw2
      by_cases hf0 : replyFn d false ∅ f = true
      · exfalso
        exact hw1.2 ((replyFn_true_of_false w₁ f hf0).trans hf0.symm)
      · have hf0' : replyFn d false ∅ f = false := Bool.eq_false_iff.mpr hf0
        have ht1 : replyFn d true w₁ f = true := by
          cases h : replyFn d true w₁ f
          · exfalso; exact hw1.2 (h.trans hf0'.symm)
          · rfl
        have ht2 : replyFn d true w₂ f = true := by
          cases h : replyFn d true w₂ f
          · exfalso; exact hw2.2 (h.trans hf0'.symm)
          · rfl
        have hp1 : passes d f w₁ := by
          rcases (replyFn_iff true w₁ f).mp ht1 with ⟨x, hlx, hpx⟩
          rcases (liveFn_true_iff w₁ x).mp hlx with hne | rfl
          · exfalso
            have hft : replyFn d false ∅ f = true :=
              (replyFn_iff false ∅ f).mpr ⟨x, (liveFn_false_iff ∅ x).mpr hne, hpx⟩
            rw [hf0'] at hft; exact Bool.false_ne_true hft
          · rwa [baseX_of_subset hw1.1] at hpx
        have hp2 : passes d f w₂ := by
          rcases (replyFn_iff true w₂ f).mp ht2 with ⟨x, hlx, hpx⟩
          rcases (liveFn_true_iff w₂ x).mp hlx with hne | rfl
          · exfalso
            have hft : replyFn d false ∅ f = true :=
              (replyFn_iff false ∅ f).mpr ⟨x, (liveFn_false_iff ∅ x).mpr hne, hpx⟩
            rw [hf0'] at hft; exact Bool.false_ne_true hft
          · rwa [baseX_of_subset hw2.1] at hpx
        exact at_most_one_target f hf0' hw1.1 hw2.1 hp1 hp2
    calc
      ((extraSet d).powerset.filter (fun w =>
          runPrefix ask true w (m + 1) ≠ runPrefix ask false ∅ (m + 1))).card
          ≤ (prev ∪ fresh).card := Finset.card_le_card hsub
      _ ≤ prev.card + fresh.card := Finset.card_union_le prev fresh
      _ ≤ m + 1 := Nat.add_le_add (ih (by omega)) hfresh_le

private lemma runPrefix_full {d k : Nat} (ask : Fin k → List Bool → Signing d)
    (on : Bool) (w : Bits d) :
    runPrefix ask on w k =
      (List.finRange k).foldl (fun h j => h ++ [replyFn d on w (ask j h)]) [] := by
  unfold runPrefix
  have htake : (List.finRange k).take k = List.finRange k :=
    List.take_of_length_le (by simp)
  rw [htake]

private lemma foldl_const_false {k : Nat} (g : Fin k → List Bool → Bool)
    (hg : ∀ j h, g j h = false) :
    ∀ (l : List (Fin k)) (acc : List Bool),
      (∀ b ∈ acc, b = false) →
      ∀ b ∈ l.foldl (fun h j => h ++ [g j h]) acc, b = false := by
  intro l
  induction l with
  | nil => intro acc hacc b hb; exact hacc b hb
  | cons j rest ih =>
    intro acc hacc b hb
    simp only [List.foldl_cons] at hb
    refine ih (acc ++ [g j acc]) ?_ b hb
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hacc x hx
    · exact hg j acc

private lemma foldl_mem_of_hit {k : Nat} (g : Fin k → List Bool → Bool) :
    ∀ (l : List (Fin k)) (acc : List Bool),
      (∃ j ∈ l, ∀ h, g j h = true) →
      true ∈ l.foldl (fun h j => h ++ [g j h]) acc := by
  intro l
  induction l with
  | nil => rintro acc ⟨j, hj, _⟩; simp at hj
  | cons j₀ rest ih =>
    intro acc ⟨j, hj, htrue⟩
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at hj
    rcases hj with rfl | hmem
    · have hpres : ∀ (l' : List (Fin k)) (a : List Bool),
          true ∈ a → true ∈ l'.foldl (fun h i => h ++ [g i h]) a := by
        intro l'
        induction l' with
        | nil => intro a ha; exact ha
        | cons i rs ihr =>
          intro a ha
          simp only [List.foldl_cons]
          exact ihr _ (List.mem_append_left _ ha)
      apply hpres
      rw [htrue acc]
      simp
    · exact ih (acc ++ [g j₀ acc]) ⟨j, hmem, htrue⟩

theorem main_proof :
    ∀ (d k p q : Nat), 2 * p < q →
      let Site := Fin (d + 2)
      let Bits := Finset Site
      let cube := (Finset.univ : Finset Bits)
      let sites := (Finset.univ : Finset Site)
      let extra := sites \ ({0, 1} : Bits)
      let Signing := Site → Bool × Bool
      let live := fun (on : Bool) (w x : Bits) =>
        let a := decide ((0 : Site) ∈ x)
        let b := decide ((1 : Site) ∈ x)
        !(a && b) && (if on then !(a && b) else a || b) &&
          extra.toList.all (fun j => a || b || (decide (j ∈ x) == decide (j ∈ w)))
      let reply := fun (on : Bool) (w : Bits) (f : Signing) => cube.toList.any (fun x =>
        live on w x && sites.toList.all (fun i =>
          (decide (i ∈ x), decide ((i + 1 : Site) ∈ x)) != f i))
      (∃ N : Nat, 0 < N ∧ ∃ ask : Fin N → Fin k → List Bool → Signing,
        ∃ answer : Fin N → List Bool → Bool, ∀ (on : Bool) (w : Bits),
          let coins := (Finset.univ : Finset (Fin N))
          let bad := coins.filter (fun c => answer c ((List.finRange k).foldl (fun h j =>
            h ++ [reply on w (ask c j h)]) ([] : List Bool)) != on)
          q * bad.card ≤ p * N) ↔
        (2 ^ d) * (q - 2 * p) ≤ k * (q - p) := by
  intro d k p q h2pq
  dsimp only
  constructor
  · rintro ⟨N, hN, ask, answer, hbound⟩
    by_cases hkd : 2 ^ d ≤ k
    · calc
        (2 ^ d) * (q - 2 * p) ≤ (2 ^ d) * (q - p) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ k * (q - p) := Nat.mul_le_mul_right _ hkd
    · push_neg at hkd
      let W : Finset (Bits d) := (extraSet d).powerset
      have hWcard : W.card = 2 ^ d := card_extraSet_powerset d
      let trace := fun (on : Bool) (w : Bits d) (c : Fin N) =>
        (List.finRange k).foldl (fun h j => h ++ [replyFn d on w (ask c j h)]) ([] : List Bool)
      let B0 : Finset (Fin N) :=
        Finset.univ.filter (fun c => (answer c (trace false ∅ c) != false) = true)
      let G : Finset (Fin N) :=
        Finset.univ.filter (fun c => answer c (trace false ∅ c) = false)
      have hB0 : q * B0.card ≤ p * N := hbound false ∅
      have hGB0 : G.card + B0.card = N := by
        have hdisj : Disjoint G B0 := by
          rw [Finset.disjoint_left]
          intro c hcG hcB
          simp only [G, B0, Finset.mem_filter, Finset.mem_univ, true_and] at hcG hcB
          rw [hcG] at hcB
          exact Bool.false_ne_true hcB
        have hunion : G ∪ B0 = Finset.univ := by
          ext c
          simp only [Finset.mem_union, G, B0, Finset.mem_filter, Finset.mem_univ, true_and,
            iff_true]
          cases answer c (trace false ∅ c) <;> simp
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
      have hG_lb : (q - p) * N ≤ q * G.card := by
        have h1 : q * G.card + q * B0.card = q * N := by
          rw [← Nat.mul_add, hGB0]
        have hpq : p ≤ q := by omega
        have h2 : (q - p) * N + p * N = q * N := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hpq]
        omega
      let badT (w : Bits d) : Finset (Fin N) :=
        Finset.univ.filter (fun c => (answer c (trace true w c) != true) = true)
      have hsum_ub : q * (∑ w ∈ W, (badT w).card) ≤ (2 ^ d) * p * N := by
        rw [Finset.mul_sum]
        calc
          ∑ w ∈ W, q * (badT w).card ≤ ∑ _w ∈ W, p * N := by
            refine Finset.sum_le_sum (fun w _ => hbound true w)
          _ = W.card * (p * N) := by rw [Finset.sum_const, smul_eq_mul]
          _ = (2 ^ d) * p * N := by rw [hWcard, Nat.mul_assoc]
      have hsum_swap : ∑ w ∈ W, (badT w).card =
          ∑ c : Fin N, (W.filter (fun w => (answer c (trace true w c) != true) = true)).card := by
        have hL : ∑ w ∈ W, (badT w).card =
            ∑ w ∈ W, ∑ c : Fin N, if (answer c (trace true w c) != true) = true then 1 else 0 := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          dsimp only [badT]
          rw [Finset.card_filter]
        have hR : ∑ c : Fin N, (W.filter (fun w => (answer c (trace true w c) != true) = true)).card =
            ∑ c : Fin N, ∑ w ∈ W, if (answer c (trace true w c) != true) = true then 1 else 0 := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.card_filter]
        rw [hL, hR, Finset.sum_comm]
      have hsum_lb : G.card * (2 ^ d - k) ≤ ∑ w ∈ W, (badT w).card := by
        rw [hsum_swap]
        calc
          G.card * (2 ^ d - k) = ∑ _c ∈ G, (2 ^ d - k) := by
            rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ c ∈ G, (W.filter (fun w => (answer c (trace true w c) != true) = true)).card := by
            refine Finset.sum_le_sum (fun c hcG => ?_)
            have hcf : answer c (trace false ∅ c) = false := (Finset.mem_filter.mp hcG).2
            let Hit := W.filter (fun w => trace true w c ≠ trace false ∅ c)
            have hHit_le : Hit.card ≤ k := by
              have h := card_diff_le (ask c) k (le_refl k)
              simpa only [Hit, W, trace, runPrefix_full] using h
            have hsub : W \ Hit ⊆
                W.filter (fun w => (answer c (trace true w c) != true) = true) := by
              intro w hw
              simp only [Finset.mem_sdiff, Hit, Finset.mem_filter, not_and, not_not] at hw
              refine Finset.mem_filter.mpr ⟨hw.1, ?_⟩
              rw [hw.2 hw.1, hcf]
              decide
            have hdiff : (W \ Hit).card = W.card - Hit.card := by
              rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ W)]
            have hle := Finset.card_le_card hsub
            rw [hdiff, hWcard] at hle
            omega
          _ ≤ ∑ c : Fin N, (W.filter (fun w => (answer c (trace true w c) != true) = true)).card := by
            refine Finset.sum_le_sum_of_subset (Finset.subset_univ G)
      have hcomb : (q - p) * N * (2 ^ d - k) ≤ (2 ^ d) * p * N := by
        calc
          (q - p) * N * (2 ^ d - k) ≤ (q * G.card) * (2 ^ d - k) :=
            Nat.mul_le_mul_right _ hG_lb
          _ = q * (G.card * (2 ^ d - k)) := by ring
          _ ≤ q * (∑ w ∈ W, (badT w).card) := Nat.mul_le_mul_left _ hsum_lb
          _ ≤ (2 ^ d) * p * N := hsum_ub
      have hcancel : (q - p) * (2 ^ d - k) ≤ (2 ^ d) * p := by
        have hrew : (q - p) * (2 ^ d - k) * N ≤ (2 ^ d) * p * N := by
          have : (q - p) * N * (2 ^ d - k) = (q - p) * (2 ^ d - k) * N := by ring
          omega
        exact Nat.le_of_mul_le_mul_right hrew hN
      have h1 : (q - p) * (2 ^ d - k) + (q - p) * k = (q - p) * (2 ^ d) := by
        rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hkd)]
      have h2 : (2 ^ d) * (q - 2 * p) + (2 ^ d) * p = (q - p) * (2 ^ d) := by
        rw [← Nat.mul_add, Nat.mul_comm (q - p)]
        congr 1
        omega
      have h3 : (q - p) * k = k * (q - p) := Nat.mul_comm _ _
      omega
  · intro hineq
    let M : Nat := 2 ^ d
    have hMpos : 0 < M := Nat.two_pow_pos d
    have hqpos : 0 < q := by omega
    let W : Finset (Bits d) := (extraSet d).powerset
    have hWcard : Fintype.card W = M := by
      rw [Fintype.card_coe]
      exact card_extraSet_powerset d
    let e : Fin M ≃ W := (Fintype.equivFinOfCardEq hWcard).symm
    let N : Nat := q * M
    have hNpos : 0 < N := Nat.mul_pos hqpos hMpos
    let ask : Fin N → Fin k → List Bool → Signing d := fun c j _ =>
      if c.val / M < p then
        fun _ => (false, false)
      else
        pointSigning d (e ⟨(c.val % M + j.val) % M, Nat.mod_lt _ hMpos⟩).1
    let answer : Fin N → List Bool → Bool := fun c h =>
      if c.val / M < p then true else h.any id
    refine ⟨N, hNpos, ask, answer, ?_⟩
    intro on w
    cases on
    · -- on = false
      let badF : Finset (Fin N) :=
        Finset.univ.filter (fun c => (answer c ((List.finRange k).foldl (fun h j =>
          h ++ [replyFn d false w (ask c j h)]) ([] : List Bool)) != false) = true)
      have hsub : badF ⊆ Finset.univ.filter (fun c : Fin N => c.val < p * M) := by
        intro c hc
        simp only [badF, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        by_contra hge
        have hdiv : ¬ (c.val / M < p) := by
          intro hlt
          have := Nat.lt_of_div_lt_div (a := c.val) (b := p * M) (c := M) (by
            rwa [Nat.mul_div_cancel p hMpos])
          omega
        have hall_false : ∀ b ∈ (List.finRange k).foldl (fun h j =>
            h ++ [replyFn d false w (ask c j h)]) ([] : List Bool), b = false := by
          apply foldl_const_false (fun j h => replyFn d false w (ask c j h))
          · intro j _
            simp only [ask, hdiv, ↓reduceIte]
            exact replyFn_pointSigning_false
              (Finset.mem_powerset.mp (e ⟨(c.val % M + j.val) % M, Nat.mod_lt _ hMpos⟩).2) w
          · intro b hb; simp at hb
        have hany : ((List.finRange k).foldl (fun h j =>
            h ++ [replyFn d false w (ask c j h)]) ([] : List Bool)).any id = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          rw [List.any_eq_true] at ht
          rcases ht with ⟨b, hb, hbid⟩
          rw [hall_false b hb] at hbid
          exact Bool.false_ne_true hbid
        simp only [answer, hdiv, ↓reduceIte, hany] at hc
        exact Bool.false_ne_true hc
      have hcard_lt : (Finset.univ.filter (fun c : Fin N => c.val < p * M)).card = p * M := by
        have hpMN : p * M ≤ N := Nat.mul_le_mul_right M (by omega)
        let emb : Fin (p * M) ↪ Fin N :=
          ⟨fun x => ⟨x.val, lt_of_lt_of_le x.isLt hpMN⟩,
            fun x y h => by dsimp only at h; exact Fin.ext (congrArg (fun z : Fin N => z.val) h)⟩
        have heq : Finset.univ.filter (fun c : Fin N => c.val < p * M) = Finset.univ.map emb := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
          constructor
          · intro hc; exact ⟨⟨c.val, hc⟩, Fin.ext rfl⟩
          · rintro ⟨x, rfl⟩; exact x.isLt
        rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
      have hle : badF.card ≤ p * M := by
        calc badF.card ≤ (Finset.univ.filter (fun c : Fin N => c.val < p * M)).card :=
              Finset.card_le_card hsub
          _ = p * M := hcard_lt
      calc
        q * badF.card ≤ q * (p * M) := Nat.mul_le_mul_left q hle
        _ = p * N := by dsimp only [N]; ring
    · -- on = true
      let badT : Finset (Fin N) :=
        Finset.univ.filter (fun c => (answer c ((List.finRange k).foldl (fun h j =>
          h ++ [replyFn d true w (ask c j h)]) ([] : List Bool)) != true) = true)
      let w₀ : W := ⟨baseX d w, Finset.mem_powerset.mpr (baseX_subset_extra w)⟩
      let idx : Fin M := e.symm w₀
      by_cases hMk : M ≤ k
      · have hemp : badT = ∅ := by
          ext c
          simp only [badT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false]
          by_cases hdiv : c.val / M < p
          · simp [answer, hdiv]
          · simp only [answer, hdiv, ↓reduceIte]
            set s := c.val % M
            have hs : s < M := Nat.mod_lt _ hMpos
            let jval := (idx.val + M - s) % M
            have hjlt : jval < k := lt_of_lt_of_le (Nat.mod_lt _ hMpos) hMk
            have hmod : (s + jval) % M = idx.val := by
              have hmod_add : ∀ a b : Nat, (a + b % M) % M = (a + b) % M := by
                intro a b
                rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have h1 : (s + jval) % M = (s + (idx.val + M - s)) % M :=
                hmod_add s (idx.val + M - s)
              rw [h1]
              have h2 : s + (idx.val + M - s) = idx.val + M := by omega
              rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt idx.isLt]
            have hmem : true ∈ (List.finRange k).foldl (fun h j =>
                h ++ [replyFn d true w (ask c j h)]) ([] : List Bool) := by
              refine foldl_mem_of_hit (fun j h => replyFn d true w (ask c j h))
                (List.finRange k) [] ⟨⟨jval, hjlt⟩, List.mem_finRange _, ?_⟩
              intro _
              simp only [ask, hdiv, ↓reduceIte]
              have hfidx : (⟨(s + jval) % M, Nat.mod_lt _ hMpos⟩ : Fin M) = idx :=
                Fin.ext hmod
              rw [hfidx]
              have hew : (e idx).1 = baseX d w := by
                change (e (e.symm w₀)).1 = baseX d w
                rw [Equiv.apply_symm_apply]
              rw [replyFn_pointSigning_true (Finset.mem_powerset.mp (e idx).2) w, hew]
              simp
            have hany : ((List.finRange k).foldl (fun h j =>
                h ++ [replyFn d true w (ask c j h)]) ([] : List Bool)).any id = true :=
              List.any_eq_true.mpr ⟨true, hmem, rfl⟩
            rw [hany]
            decide
        change q * badT.card ≤ p * N
        rw [hemp]; simp
      · push_neg at hMk
        let goodS : Finset (Fin M) :=
          Finset.univ.filter (fun s : Fin M => ∃ j : Fin k, (s.val + j.val) % M = idx.val)
        have hgood_ge : k ≤ goodS.card := by
          let emb : Fin k ↪ Fin M :=
            ⟨fun j => ⟨(idx.val + M - j.val) % M, Nat.mod_lt _ hMpos⟩, by
              intro j₁ j₂ h
              have hv := congrArg Fin.val h
              change (idx.val + M - j₁.val) % M = (idx.val + M - j₂.val) % M at hv
              have hj1 : j₁.val < M := lt_trans j₁.isLt hMk
              have hj2 : j₂.val < M := lt_trans j₂.isLt hMk
              have h1 : ((idx.val + M - j₁.val) + j₁.val) % M = idx.val := by
                have : idx.val + M - j₁.val + j₁.val = idx.val + M := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt idx.isLt]
              have h2 : ((idx.val + M - j₂.val) + j₂.val) % M = idx.val := by
                have : idx.val + M - j₂.val + j₂.val = idx.val + M := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt idx.isLt]
              by_cases hc1 : j₁.val ≤ idx.val
              · have hm1 : (idx.val + M - j₁.val) % M = idx.val - j₁.val := by
                  have : idx.val + M - j₁.val = (idx.val - j₁.val) + M := by omega
                  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                by_cases hc2 : j₂.val ≤ idx.val
                · have hm2 : (idx.val + M - j₂.val) % M = idx.val - j₂.val := by
                    have : idx.val + M - j₂.val = (idx.val - j₂.val) + M := by omega
                    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                  rw [hm1, hm2] at hv
                  exact Fin.ext (by omega)
                · have hm2 : (idx.val + M - j₂.val) % M = idx.val + M - j₂.val :=
                    Nat.mod_eq_of_lt (by omega)
                  rw [hm1, hm2] at hv
                  omega
              · have hm1 : (idx.val + M - j₁.val) % M = idx.val + M - j₁.val :=
                  Nat.mod_eq_of_lt (by omega)
                by_cases hc2 : j₂.val ≤ idx.val
                · have hm2 : (idx.val + M - j₂.val) % M = idx.val - j₂.val := by
                    have : idx.val + M - j₂.val = (idx.val - j₂.val) + M := by omega
                    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                  rw [hm1, hm2] at hv
                  omega
                · have hm2 : (idx.val + M - j₂.val) % M = idx.val + M - j₂.val :=
                    Nat.mod_eq_of_lt (by omega)
                  rw [hm1, hm2] at hv
                  exact Fin.ext (by omega)⟩
          have hsub : Finset.univ.map emb ⊆ goodS := by
            intro s hs
            rcases Finset.mem_map.mp hs with ⟨j, _, rfl⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, ?_⟩
            have hj : j.val < M := lt_trans j.isLt hMk
            change ((idx.val + M - j.val) % M + j.val) % M = idx.val
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have hadd : idx.val + M - j.val + j.val = idx.val + M := by omega
            rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt idx.isLt]
          have hle := Finset.card_le_card hsub
          rwa [Finset.card_map, Finset.card_univ, Fintype.card_fin] at hle
        let badS : Finset (Fin M) := Finset.univ \ goodS
        have hbadS_le : badS.card ≤ M - k := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
          omega
        let badA : Finset (Fin q) := Finset.univ.filter (fun a : Fin q => p ≤ a.val)
        have hbadA_card : badA.card = q - p := by
          have hgoodA : (Finset.univ.filter (fun a : Fin q => a.val < p)).card = p := by
            have hpq : p ≤ q := by omega
            let embA : Fin p ↪ Fin q :=
              ⟨fun x => ⟨x.val, lt_of_lt_of_le x.isLt hpq⟩,
                fun x y h => by dsimp only at h; exact Fin.ext (congrArg (fun z : Fin q => z.val) h)⟩
            have heq : Finset.univ.filter (fun a : Fin q => a.val < p) = Finset.univ.map embA := by
              ext a
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
              constructor
              · intro ha; exact ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
              · rintro ⟨x, rfl⟩; exact x.isLt
            rw [heq, Finset.card_map, Finset.card_univ, Fintype.card_fin]
          have hcomp : badA = Finset.univ \ Finset.univ.filter (fun a : Fin q => a.val < p) := by
            ext a
            simp only [badA, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
            omega
          rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
            hgoodA]
        let pairOf : Fin N ↪ Fin q × Fin M :=
          ⟨fun c => (⟨c.val / M, Nat.div_lt_of_lt_mul (by simp [N, Nat.mul_comm])⟩,
            ⟨c.val % M, Nat.mod_lt _ hMpos⟩), by
            intro c₁ c₂ h
            have h1 := congrArg (fun x => x.1.val) h
            have h2 := congrArg (fun x => x.2.val) h
            dsimp only at h1 h2
            apply Fin.ext
            have e1 := Nat.div_add_mod c₁.val M
            have e2 := Nat.div_add_mod c₂.val M
            rw [← e1, ← e2, h1, h2]⟩
        have hmap_sub : badT.map pairOf ⊆ badA ×ˢ badS := by
          intro x hx
          rcases Finset.mem_map.mp hx with ⟨c, hc, rfl⟩
          simp only [badT, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          have hdiv : ¬ (c.val / M < p) := by
            intro hlt
            simp [answer, hlt] at hc
          refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            change p ≤ c.val / M; omega⟩, ?_⟩
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
          intro hgood
          rcases (Finset.mem_filter.mp hgood).2 with ⟨j, hj⟩
          have hmem : true ∈ (List.finRange k).foldl (fun h j' =>
              h ++ [replyFn d true w (ask c j' h)]) ([] : List Bool) := by
            refine foldl_mem_of_hit (fun j' h => replyFn d true w (ask c j' h))
              (List.finRange k) [] ⟨j, List.mem_finRange j, ?_⟩
            intro _
            simp only [ask, hdiv, ↓reduceIte]
            have hfidx : (⟨(c.val % M + j.val) % M, Nat.mod_lt _ hMpos⟩ : Fin M) = idx :=
              Fin.ext hj
            rw [hfidx]
            have hew : (e idx).1 = baseX d w := by
              change (e (e.symm w₀)).1 = baseX d w
              rw [Equiv.apply_symm_apply]
            rw [replyFn_pointSigning_true (Finset.mem_powerset.mp (e idx).2) w, hew]
            simp
          have hany : ((List.finRange k).foldl (fun h j' =>
              h ++ [replyFn d true w (ask c j' h)]) ([] : List Bool)).any id = true :=
            List.any_eq_true.mpr ⟨true, hmem, rfl⟩
          simp only [answer, hdiv, ↓reduceIte, hany] at hc
          exact Bool.false_ne_true hc
        have hbadT_le : badT.card ≤ (q - p) * (M - k) := by
          calc
            badT.card = (badT.map pairOf).card := (Finset.card_map pairOf).symm
            _ ≤ (badA ×ˢ badS).card := Finset.card_le_card hmap_sub
            _ = badA.card * badS.card := Finset.card_product badA badS
            _ ≤ (q - p) * (M - k) := by
              rw [hbadA_card]
              exact Nat.mul_le_mul_left _ hbadS_le
        have hcore : (q - p) * (M - k) ≤ p * M := by
          have hineqM : M * (q - 2 * p) ≤ k * (q - p) := hineq
          have h1 : (q - p) * (M - k) + (q - p) * k = (q - p) * M := by
            rw [← Nat.mul_add, Nat.sub_add_cancel (le_of_lt hMk)]
          have h2 : M * (q - 2 * p) + M * p = (q - p) * M := by
            rw [← Nat.mul_add, Nat.mul_comm (q - p)]
            congr 1
            omega
          have h3 : (q - p) * k = k * (q - p) := Nat.mul_comm _ _
          have h4 : p * M = M * p := Nat.mul_comm _ _
          omega
        calc
          q * badT.card ≤ q * ((q - p) * (M - k)) := Nat.mul_le_mul_left q hbadT_le
          _ ≤ q * (p * M) := Nat.mul_le_mul_left q hcore
          _ = p * N := by dsimp only [N]; ring

end PEqualNP.Outside.L_lib_1160

theorem PEqualNP.Outside.L_lib_1160 :
∀ (d k p q : Nat), 2 * p < q →
  let Site := Fin (d + 2)
  let Bits := Finset Site
  let cube := (Finset.univ : Finset Bits)
  let sites := (Finset.univ : Finset Site)
  let extra := sites \ ({0, 1} : Bits)
  let Signing := Site → Bool × Bool
  let live := fun (on : Bool) (w x : Bits) =>
    let a := decide ((0 : Site) ∈ x)
    let b := decide ((1 : Site) ∈ x)
    !(a && b) && (if on then !(a && b) else a || b) &&
      extra.toList.all (fun j => a || b || (decide (j ∈ x) == decide (j ∈ w)))
  let reply := fun (on : Bool) (w : Bits) (f : Signing) => cube.toList.any (fun x =>
    live on w x && sites.toList.all (fun i =>
      (decide (i ∈ x), decide ((i + 1 : Site) ∈ x)) != f i))
  (∃ N : Nat, 0 < N ∧ ∃ ask : Fin N → Fin k → List Bool → Signing,
    ∃ answer : Fin N → List Bool → Bool, ∀ (on : Bool) (w : Bits),
      let coins := (Finset.univ : Finset (Fin N))
      let bad := coins.filter (fun c => answer c ((List.finRange k).foldl (fun h j =>
        h ++ [reply on w (ask c j h)]) ([] : List Bool)) != on)
      q * bad.card ≤ p * N) ↔
    (2 ^ d) * (q - 2 * p) ≤ k * (q - p) :=
  PEqualNP.Outside.L_lib_1160.main_proof
