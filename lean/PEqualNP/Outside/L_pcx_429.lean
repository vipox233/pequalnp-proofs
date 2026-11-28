import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_429

-- The Rado helpers are from lean/PEqualNP/Outside/L_gct_114.lean
-- at 0afd423ba0b356e17703f90445968435e121a097, with their namespace adapted.

open Submodule Module

variable {W ι : Type*}

/-- The union of the sets `A j` over `j ∈ s`. -/
private def un (A : ι → Finset W) (s : Finset ι) : Set W := ⋃ j ∈ s, (A j : Set W)

private lemma un_finite (A : ι → Finset W) (s : Finset ι) : (un A s).Finite :=
  s.finite_toSet.biUnion fun j _ => (A j).finite_toSet

private lemma un_insert [DecidableEq ι] (A : ι → Finset W) (i : ι) (s : Finset ι) :
    un A (insert i s) = (A i : Set W) ∪ un A s := by
  simp only [un, Finset.set_biUnion_insert]

private lemma un_union [DecidableEq ι] (A : ι → Finset W) (s t : Finset ι) :
    un A (s ∪ t) = un A s ∪ un A t := by
  simp only [un, Finset.set_biUnion_union]

private lemma un_mono (A : ι → Finset W) {s t : Finset ι} (h : s ⊆ t) : un A s ⊆ un A t :=
  Set.biUnion_subset_biUnion_left (fun _ hx => h hx)

private lemma un_update_of_not_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∉ s) : un (Function.update A i B) s = un A s := by
  unfold un
  refine Set.iUnion₂_congr fun j hj => ?_
  rw [Function.update_of_ne (by rintro rfl; exact h hj)]

private lemma un_update_of_mem [DecidableEq ι] (A : ι → Finset W) (i : ι) (B : Finset W)
    (s : Finset ι) (h : i ∈ s) :
    un (Function.update A i B) s = (B : Set W) ∪ un A (s.erase i) := by
  conv_lhs => rw [← Finset.insert_erase h]
  rw [un_insert, un_update_of_not_mem _ _ _ _ (Finset.notMem_erase i s),
    Function.update_self]

variable {K : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- The rank condition: every index set `s` has at most as many indices as the dimension of
the span of its union. -/
private def Good (K : Type*) [Field K] [Module K W] (A : ι → Finset W) : Prop :=
  ∀ s : Finset ι, s.card ≤ finrank K (span K (un A s))

private lemma finrank_span_mono {X Y : Set W} (hY : Y.Finite) (h : X ⊆ Y) :
    finrank K (span K X) ≤ finrank K (span K Y) := by
  have := FiniteDimensional.span_of_finite K hY
  exact Submodule.finrank_mono (span_mono h)

/-- If removing `c` from `A i` breaks the rank condition, there is an index set `t` avoiding
`i` with `dim span ((A i).erase c ∪ un A t) ≤ |t|`. -/
private lemma bad_erase [DecidableEq ι] [DecidableEq W] (A : ι → Finset W) (hA : Good K A) (i : ι)
    (c : W) (h : ¬ Good K (Function.update A i ((A i).erase c))) :
    ∃ t : Finset ι, i ∉ t ∧
      finrank K (span K ((((A i).erase c : Finset W) : Set W) ∪ un A t)) ≤ t.card := by
  simp only [Good, not_forall, not_le] at h
  obtain ⟨s, hs⟩ := h
  by_cases hi : i ∈ s
  · refine ⟨s.erase i, Finset.notMem_erase i s, ?_⟩
    rw [un_update_of_mem _ _ _ _ hi] at hs
    have := Finset.card_erase_add_one hi
    omega
  · rw [un_update_of_not_mem _ _ _ _ hi] at hs
    exact absurd (hA s) (not_le.mpr hs)

/-- The Rado / Mirsky reduction step: of two distinct elements of `A i`, one can be removed
keeping the rank condition. -/
private lemma erase_good [DecidableEq ι] [DecidableEq W] (A : ι → Finset W) (hA : Good K A) (i : ι)
    {a b : W} (ha : a ∈ A i) (_hb : b ∈ A i) (hab : a ≠ b) :
    Good K (Function.update A i ((A i).erase a)) ∨
      Good K (Function.update A i ((A i).erase b)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨t1, hi1, h1⟩ := bad_erase A hA i a hcon.1
  obtain ⟨t2, hi2, h2⟩ := bad_erase A hA i b hcon.2
  set X : Set W := (((A i).erase a : Finset W) : Set W) ∪ un A t1 with hX
  set Y : Set W := (((A i).erase b : Finset W) : Set W) ∪ un A t2 with hY
  have hXf : X.Finite := ((A i).erase a).finite_toSet.union (un_finite A t1)
  have hYf : Y.Finite := ((A i).erase b).finite_toSet.union (un_finite A t2)
  have : FiniteDimensional K (span K X) := FiniteDimensional.span_of_finite K hXf
  have : FiniteDimensional K (span K Y) := FiniteDimensional.span_of_finite K hYf
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (span K X) (span K Y)
  -- the union side
  have hU : un A (insert i (t1 ∪ t2)) ⊆ X ∪ Y := by
    rw [un_insert, un_union]
    intro x hx
    rcases hx with hx | hx | hx
    · by_cases hxa : x = a
      · subst hxa
        exact Or.inr (Or.inl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hab, ha⟩)))
      · exact Or.inl (Or.inl (by simp [hxa, hx]))
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)
  have hi12 : i ∉ t1 ∪ t2 := by simp [hi1, hi2]
  have hcardU := hA (insert i (t1 ∪ t2))
  rw [Finset.card_insert_of_notMem hi12] at hcardU
  have hsup : finrank K (span K (un A (insert i (t1 ∪ t2)))) ≤ finrank K ↥(span K X ⊔ span K Y) := by
    rw [← Submodule.span_union]
    exact finrank_span_mono (hXf.union hYf) hU
  -- the intersection side
  have hinf : finrank K (span K (un A (t1 ∩ t2))) ≤ finrank K ↥(span K X ⊓ span K Y) := by
    have : FiniteDimensional K ↥(span K X ⊓ span K Y) :=
      Submodule.finiteDimensional_inf_left _ _
    refine Submodule.finrank_mono (le_inf (span_mono ?_) (span_mono ?_))
    · exact (un_mono A Finset.inter_subset_left).trans Set.subset_union_right
    · exact (un_mono A Finset.inter_subset_right).trans Set.subset_union_right
  have hcardI := hA (t1 ∩ t2)
  have hc := Finset.card_union_add_card_inter t1 t2
  omega

/-- Rado's theorem, by induction on the total size of the sets. -/
private theorem rado_aux [Fintype ι] [DecidableEq ι] [DecidableEq W] :
    ∀ n : ℕ, ∀ A : ι → Finset W, ∑ j, (A j).card = n → Good K A →
      ∃ f : ι → W, (∀ j, f j ∈ A j) ∧ LinearIndependent K f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hn hA
  by_cases hbig : ∃ i, 1 < (A i).card
  · obtain ⟨i, hi⟩ := hbig
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hi
    have key : ∃ c ∈ A i, Good K (Function.update A i ((A i).erase c)) := by
      rcases erase_good A hA i ha hb hab with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    obtain ⟨c, hc, hgood⟩ := key
    set A' := Function.update A i ((A i).erase c) with hA'
    have hlt : ∑ j, (A' j).card < n := by
      rw [← hn]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
      · by_cases hj : j = i
        · subst hj; simp only [hA', Function.update_self]
          exact Finset.card_erase_le
        · simp only [hA', Function.update_of_ne hj, le_refl]
      · simp only [hA', Function.update_self]
        exact Finset.card_erase_lt_of_mem hc
    obtain ⟨f, hf, hli⟩ := ih _ hlt A' rfl hgood
    refine ⟨f, fun j => ?_, hli⟩
    have := hf j
    by_cases hj : j = i
    · subst hj; simp only [hA', Function.update_self] at this
      exact Finset.mem_of_mem_erase this
    · simpa only [hA', Function.update_of_ne hj] using this
  · push Not at hbig
    have hone : ∀ j, ∃ v, A j = {v} := by
      intro j
      refine Finset.card_eq_one.mp (le_antisymm (hbig j) ?_)
      have h1 := hA {j}
      have hunj : un A {j} = (A j : Set W) := by simp [un]
      rw [hunj, Finset.card_singleton] at h1
      rw [Nat.one_le_iff_ne_zero] at h1 ⊢
      intro h0
      rw [Finset.card_eq_zero] at h0
      apply h1
      simp [h0]
    choose f hf using hone
    refine ⟨f, fun j => by simp [hf j], ?_⟩
    rw [linearIndependent_iff_card_le_finrank_span]
    have h := hA Finset.univ
    have hr : un A Finset.univ = Set.range f := by
      ext x; simp [un, hf, eq_comm]
    rw [hr, Finset.card_univ] at h
    exact h

private abbrev Pad (d : ℕ) := Fin d → ZMod 2

private noncomputable def padded {E : Type*} [Fintype E] [Zero E] (A : ι → Finset E) (d : ℕ)
    (i : ι) : Finset (E × Pad d) :=
  letI := Classical.decEq E
  Finset.univ.filter fun v => v.1 ∈ A i ∨ v.1 = 0

private lemma mem_padded {E : Type*} [Fintype E] [Zero E] (A : ι → Finset E)
    (d : ℕ) (i : ι) (v : E × Pad d) :
    v ∈ padded A d i ↔ v.1 ∈ A i ∨ v.1 = 0 := by
  classical
  simp [padded]

private lemma finrank_prod_top {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (P : Submodule (ZMod 2) E) (d : ℕ) :
    finrank (ZMod 2) (P.prod (⊤ : Submodule (ZMod 2) (Pad d))) =
      finrank (ZMod 2) P + d := by
  rw [(P.prodEquiv _).finrank_eq, Module.finrank_prod, finrank_top, Module.finrank_fin_fun]

private lemma padded_rank_ge {E : Type*} [Fintype E] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (A : ι → Finset E) (d : ℕ) {s : Finset ι}
    (hs : s.Nonempty) :
    finrank (ZMod 2) (span (ZMod 2) (un A s)) + d ≤
      finrank (ZMod 2) (span (ZMod 2) (un (padded A d) s)) := by
  classical
  let P := span (ZMod 2) (un A s)
  let Q := span (ZMod 2) (un (padded A d) s)
  have hinl : P ≤ Q.comap (LinearMap.inl (ZMod 2) E (Pad d)) := by
    apply span_le.mpr
    intro x hx
    simp only [un, Set.mem_iUnion, Finset.mem_coe] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    apply subset_span
    simp only [un, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨i, hi, (mem_padded A d i (x, 0)).mpr (Or.inl hxi)⟩
  have hinr (y : Pad d) : ((0 : E), y) ∈ Q := by
    obtain ⟨i, hi⟩ := hs
    apply subset_span
    simp only [un, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨i, hi, (mem_padded A d i (0, y)).mpr (Or.inr rfl)⟩
  have hle : P.prod (⊤ : Submodule (ZMod 2) (Pad d)) ≤ Q := by
    rintro ⟨x, y⟩ h
    have hx : (x, (0 : Pad d)) ∈ Q := hinl (Submodule.mem_prod.mp h).1
    simpa using Q.add_mem hx (hinr y)
  rw [← finrank_prod_top P d]
  exact Submodule.finrank_mono hle

-- A common extra space fills a deficit in the subset rank condition.
private lemma rado_deficit {E : Type*} [Fintype E] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] [Fintype ι]
    (A : ι → Finset E) (hA : ∀ i, (A i).Nonempty) (p : ℕ)
    (h : ∀ v : ι → E, (∀ i, v i ∈ A i) →
      finrank (ZMod 2) (span (ZMod 2) (Set.range v)) ≤ p) :
    ∃ s : Finset ι, finrank (ZMod 2) (span (ZMod 2) (un A s)) +
      (Fintype.card ι - s.card) ≤ p := by
  classical
  by_cases hp : Fintype.card ι ≤ p
  · have hnil : un A (∅ : Finset ι) = ∅ := by
      ext x
      simp [un]
    refine ⟨(∅ : Finset ι), ?_⟩
    rw [hnil, Submodule.span_empty, finrank_bot]
    simpa using hp
  by_contra hn
  push Not at hn
  let d := Fintype.card ι - (p + 1)
  have hg : Good (ZMod 2) (padded A d) := by
    intro s
    by_cases hs : s.Nonempty
    · change s.card ≤ finrank (ZMod 2) (span (ZMod 2) (un (padded A d) s))
      have hdim := padded_rank_ge A d hs
      have hn' := hn s
      have hc := Finset.card_le_univ s
      dsimp [d] at hdim ⊢
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨v, hv, hli⟩ := rado_aux _ (padded A d) rfl hg
  have hs (i : ι) : ∃ x ∈ A i, (v i).1 = x ∨ (v i).1 = 0 := by
    rcases (mem_padded A d i (v i)).mp (hv i) with hi | hi
    · exact ⟨_, hi, Or.inl rfl⟩
    · obtain ⟨x, hx⟩ := hA i
      exact ⟨x, hx, Or.inr hi⟩
  choose u hu hvu using hs
  let P := span (ZMod 2) (Set.range u)
  have hle : span (ZMod 2) (Set.range v) ≤ P.prod (⊤ : Submodule (ZMod 2) (Pad d)) := by
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine Submodule.mem_prod.mpr ⟨?_, Submodule.mem_top⟩
    rcases hvu i with hi | hi
    · rw [hi]
      exact subset_span (Set.mem_range_self i)
    · rw [hi]
      exact P.zero_mem
  have hr := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, finrank_prod_top] at hr
  have hp' := h u hu
  change finrank (ZMod 2) P ≤ p at hp'
  dsimp [d] at hr
  omega

private abbrev F := ZMod 2
private abbrev V (n : ℕ) := (Fin n → F) × (Fin n → F)
private abbrev X {r : ℕ} (m : Fin r → ℕ) := (i : Fin r) → V (m i) × F

private def q {n : ℕ} (u : V n) : F := ∑ j, u.1 j * u.2 j
private def b {n : ℕ} (u v : V n) : F := ∑ j, (u.1 j * v.2 j + u.2 j * v.1 j)
private def f {r : ℕ} {m : Fin r → ℕ} (x : X m) (i : Fin r) : F := (x i).2 + q (x i).1

private theorem radical_q_add {n : ℕ} (u v : V n) :
    q (u + v) = q u + q v + b u v := by
  simp only [q, b, ← Finset.sum_add_distrib, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  congr 1
  funext j
  ring

private theorem radical_b_add_left {n : ℕ} (u v w : V n) :
    b (u + v) w = b u w + b v w := by
  simp only [b, ← Finset.sum_add_distrib, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  congr 1
  funext j
  ring

private theorem radical_b_comm {n : ℕ} (u v : V n) : b u v = b v u := by
  unfold b
  congr 1
  funext j
  ring

private theorem radical_b_add_right {n : ℕ} (u v w : V n) :
    b u (v + w) = b u v + b u w := by
  rw [radical_b_comm u, radical_b_add_left, radical_b_comm v, radical_b_comm w]

private theorem radical_b_zero {n : ℕ} (w : V n) : b 0 w = 0 := by
  simp [b]

private theorem radical_b_smul {n : ℕ} (c : F) (u w : V n) :
    b (c • u) w = c * b u w := by
  simp only [b, Finset.mul_sum]
  congr 1
  funext j
  change (c * u.1 j) * w.2 j + (c * u.2 j) * w.1 j =
    c * (u.1 j * w.2 j + u.2 j * w.1 j)
  ring

private def rad {r : ℕ} {m : Fin r → ℕ} (S : Submodule F (X m)) : Submodule F (X m) :=
  { add_mem' := by
      intro x z hx hz
      refine ⟨S.add_mem hx.1 hz.1, fun y hy i => ?_⟩
      change b ((x i).1 + (z i).1) (y i).1 = 0
      rw [radical_b_add_left, hx.2 y hy i, hz.2 y hy i, add_zero]
    carrier := {x ∈ S | ∀ y ∈ S, ∀ i, b (x i).1 (y i).1 = 0}
    zero_mem' := ⟨S.zero_mem, fun _ _ _ => radical_b_zero _⟩
    smul_mem' := by
      intro c x hx
      refine ⟨S.smul_mem c hx.1, fun y hy i => ?_⟩
      change b (c • (x i).1) (y i).1 = 0
      rw [radical_b_smul, hx.2 y hy i, mul_zero] }

private theorem rad_le {r : ℕ} {m : Fin r → ℕ} (S : Submodule F (X m)) :
    rad S ≤ S := fun _ hx => hx.1

private theorem rad_b_zero {r : ℕ} {m : Fin r → ℕ} {S : Submodule F (X m)}
    {x y : X m} (hx : x ∈ rad S) (hy : y ∈ S) (i : Fin r) :
    b (x i).1 (y i).1 = 0 := hx.2 y hy i

private theorem radical_f_add {r : ℕ} {m : Fin r → ℕ} (a x : X m) (i : Fin r) :
    f (a + x) i = f a i + (f x i + b (a i).1 (x i).1) := by
  simp only [f, Pi.add_apply, Prod.fst_add, Prod.snd_add, radical_q_add]
  abel

private theorem radical_period {r e : ℕ} {m : Fin r → ℕ} (S : Submodule F (X m))
    (a : X m) (ask : X m →ₗ[F] (Fin e → F)) (out : (Fin e → F) → (Fin r → F))
    (h : ∀ w ∈ S, out (ask (a + w)) = f (a + w)) {x : X m} (hx : x ∈ S)
    (hask : ask x = 0) : x ∈ rad S ∧ ∀ i, f x i + b (a i).1 (x i).1 = 0 := by
  have period (w : X m) (hw : w ∈ S) (i : Fin r) :
      f x i + b ((a + w) i).1 (x i).1 = 0 := by
    have he : f (a + w + x) i = f (a + w) i := by
      have h' := h (w + x) (S.add_mem hw hx)
      rw [← add_assoc, map_add, hask, add_zero, h w hw] at h'
      exact congrFun h'.symm i
    rw [radical_f_add] at he
    exact add_left_cancel (he.trans (add_zero _).symm)
  have base : ∀ i, f x i + b (a i).1 (x i).1 = 0 := by
    simpa only [add_zero] using period 0 S.zero_mem
  refine ⟨⟨hx, fun w hw i => ?_⟩, base⟩
  have step := period w hw i
  change f x i + b ((a i).1 + (w i).1) (x i).1 = 0 at step
  rw [radical_b_add_left, ← add_assoc, base i, zero_add, radical_b_comm] at step
  exact step

private def row {r : ℕ} {m : Fin r → ℕ} (S : Submodule F (X m))
    (i : Fin r) (a : V (m i)) : Module.Dual F (rad S) where
  toFun x := f x.val i + b a (x.val i).1
  map_add' x y := by
    change f (x.val + y.val) i + b a ((x.val i).1 + (y.val i).1) =
      (f x.val i + b a (x.val i).1) + (f y.val i + b a (y.val i).1)
    rw [radical_f_add, rad_b_zero x.property (rad_le S y.property) i, add_zero,
      radical_b_add_right]
    abel
  map_smul' c x := by
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · simp [f, q, b]
    · simp

private theorem row_apply {r : ℕ} {m : Fin r → ℕ} (S : Submodule F (X m))
    (i : Fin r) (a : V (m i)) (x : rad S) :
    row S i a x = (x.val i).2 + q (x.val i).1 + b a (x.val i).1 := rfl

private theorem radical_block_nondegenerate {n : ℕ} (u : V n)
    (h : ∀ a : V n, b a u = 0) : u = 0 := by
  apply Prod.ext
  · funext j
    have hj := h (0, Pi.single j (1 : F))
    simp only [b, Pi.zero_apply, zero_mul, zero_add] at hj
    rw [Fintype.sum_eq_single j (fun k hkj => by simp [Pi.single_eq_of_ne hkj]),
      Pi.single_eq_same, one_mul] at hj
    exact hj
  · funext j
    have hj := h (Pi.single j (1 : F), 0)
    simp only [b, Pi.zero_apply, zero_mul, add_zero] at hj
    rw [Fintype.sum_eq_single j (fun k hkj => by simp [Pi.single_eq_of_ne hkj]),
      Pi.single_eq_same, one_mul] at hj
    exact hj

private theorem row_all_zero_iff {r : ℕ} {m : Fin r → ℕ} (S : Submodule F (X m))
    (i : Fin r) (x : rad S) : (∀ a, row S i a x = 0) ↔ x.val i = 0 := by
  constructor
  · intro h
    have h0 : f x.val i = 0 := by
      simpa only [row_apply, f, radical_b_zero, add_zero] using h 0
    have hV : (x.val i).1 = 0 := radical_block_nondegenerate _ (fun a => by
      have ha := h a
      change f x.val i + b a (x.val i).1 = 0 at ha
      simpa only [h0, zero_add] using ha)
    refine Prod.ext hV ?_
    simpa [f, hV, q] using h0
  · intro hx a
    simp [row_apply, hx, q, b]

private theorem row_rank_bound {r e : ℕ} {m : Fin r → ℕ} (S : Submodule F (X m))
    (h : ∀ a : X m, ∃ ask : X m →ₗ[F] (Fin e → F), ∃ out : (Fin e → F) → (Fin r → F),
      ∀ w ∈ S, out (ask (a + w)) = f (a + w))
    (a : (i : Fin r) → V (m i)) :
    Module.finrank F S + Module.finrank F (Submodule.span F (Set.range fun i => row S i (a i)))
      ≤ e + Module.finrank F (rad S) := by
  let base : X m := fun i => (a i, 0)
  obtain ⟨ask, out, hbase⟩ := h base
  let A := ask.comp S.subtype
  let K := LinearMap.ker A
  let W := Submodule.span F (Set.range fun i => row S i (a i))
  have hker (z : K) : z.val.val ∈ rad S ∧
      ∀ i, f z.val.val i + b (a i) (z.val.val i).1 = 0 :=
    radical_period S base ask out hbase z.val.property (LinearMap.mem_ker.mp z.property)
  let d : K →ₗ[F] rad S :=
    (S.subtype.comp K.subtype).codRestrict (rad S) (fun z => (hker z).1)
  let d' : K →ₗ[F] W.dualCoannihilator := d.codRestrict _ (fun z => by
    change d z ∈ ((Submodule.span F (Set.range fun i => row S i (a i))).dualCoannihilator :
      Set (rad S))
    rw [Submodule.coe_dualCoannihilator_span]
    rintro _ ⟨i, rfl⟩
    exact (hker z).2 i)
  have hdim : Module.finrank F K ≤ Module.finrank F W.dualCoannihilator :=
    LinearMap.finrank_le_finrank_of_injective (f := d') (fun _ _ hzz =>
      Subtype.ext (Subtype.ext (congrArg (fun z : W.dualCoannihilator => z.val.val) hzz)))
  have hrange : Module.finrank F (LinearMap.range A) ≤ e := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      (Submodule.finrank_le (LinearMap.range A))
  have hA : Module.finrank F (LinearMap.range A) + Module.finrank F K = Module.finrank F S :=
    LinearMap.finrank_range_add_finrank_ker A
  have hW := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  change Module.finrank F S + Module.finrank F W ≤ e + Module.finrank F (rad S)
  omega

private def geomBoxFactor {r} {m : Fin r → ℕ} (T : Finset (Fin r))
    (U : (i : Fin r) → Submodule F (V (m i))) (i : Fin r) :
    Submodule F (V (m i) × F) :=
  if i ∈ T then (U i).prod ⊤ else ⊥

private def box {r} {m : Fin r → ℕ} (T : Finset (Fin r))
    (U : (i : Fin r) → Submodule F (V (m i))) : Submodule F (X m) :=
  Submodule.pi Set.univ (geomBoxFactor T U)

private theorem mem_box {r} {m : Fin r → ℕ} (T : Finset (Fin r))
    (U : (i : Fin r) → Submodule F (V (m i))) (w : X m) :
    w ∈ box T U ↔ (∀ i ∈ T, (w i).1 ∈ U i) ∧ (∀ i : Fin r, i ∉ T → w i = 0) := by
  simp only [box, Submodule.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h
    exact ⟨fun i hi => by simpa [geomBoxFactor, hi] using h i,
      fun i hi => by simpa [geomBoxFactor, hi] using h i⟩
  · rintro ⟨hT, hTc⟩ i
    by_cases hi : i ∈ T
    · simpa [geomBoxFactor, hi] using hT i hi
    · simpa [geomBoxFactor, hi] using hTc i hi

private theorem finrank_box {r} {m : Fin r → ℕ} (T : Finset (Fin r))
    (U : (i : Fin r) → Submodule F (V (m i))) :
    Module.finrank F (box T U) = T.card + ∑ i ∈ T, Module.finrank F (U i) := by
  classical
  let E : box T U ≃ₗ[F] ((i : Fin r) → geomBoxFactor T U i) :=
    { toFun := fun w i => ⟨w.1 i, Submodule.mem_pi.mp w.2 i (Set.mem_univ i)⟩
      invFun := fun w => ⟨fun i => (w i).1, Submodule.mem_pi.mpr fun i _ => (w i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [E.finrank_eq, Module.finrank_pi_fintype]
  calc
    (∑ i : Fin r, Module.finrank F (geomBoxFactor T U i)) =
        ∑ i : Fin r, if i ∈ T then 1 + Module.finrank F (U i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      let dim := fun W : Submodule F (V (m i) × F) => Module.finrank F W
      by_cases hi : i ∈ T
      · rw [ite_eq_left hi]
        refine (congrArg dim (show geomBoxFactor T U i = (U i).prod ⊤ from ite_eq_left hi)).trans ?_
        change Module.finrank F ((U i).prod ⊤) = _
        rw [(Submodule.prodEquiv (U i) ⊤).finrank_eq, Module.finrank_prod,
          finrank_top, Module.finrank_self, Nat.add_comm]
      · rw [ite_eq_right hi]
        exact (congrArg dim (show geomBoxFactor T U i = ⊥ from ite_eq_right hi)).trans
          (finrank_bot _ _)
    _ = _ := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_add_distrib]
      simp

private def geomBilin (n : ℕ) : LinearMap.BilinForm F (V n) where
  toFun u :=
    { toFun := b u
      map_add' := radical_b_add_right u
      map_smul' := fun c v => by
        change b u (c • v) = c * b u v
        rw [radical_b_comm u, radical_b_smul, radical_b_comm v u] }
  map_add' := fun u v => LinearMap.ext fun w => radical_b_add_left u v w
  map_smul' := fun c u => LinearMap.ext fun w => radical_b_smul c u w

private theorem geomBilin_left {n} (u : V n) (h : ∀ v, geomBilin n u v = 0) :
    u = 0 :=
  radical_block_nondegenerate u (fun v => (radical_b_comm v u).trans (h v))

-- Orthogonal-dimension argument adapted from lean/PEqualNP/Outside/L_lib_118.lean
-- at 0afd423ba0b356e17703f90445968435e121a097, specialized to the coordinate form.
private theorem iso_rank_le {n} (U : Submodule F (V n))
    (h : ∀ u ∈ U, ∀ v ∈ U, b u v = 0) : Module.finrank F U ≤ n := by
  have hB : (geomBilin n).Nondegenerate := .ofSeparatingLeft geomBilin_left
  have hsub : U ≤ (geomBilin n).orthogonal U := by
    intro x hx y hy
    exact h y hy x hx
  have h1 := Submodule.finrank_mono hsub
  have h2 := LinearMap.BilinForm.finrank_orthogonal hB U
  have h3 := Submodule.finrank_le U
  have hdim : Module.finrank F (V n) = n + n := by
    simp [V, Module.finrank_prod]
  omega

private theorem geomDelta {r} {m : Fin r → ℕ} (a w : X m) (i : Fin r) :
    f (a + w) i - f a i = (w i).2 + q (w i).1 + b (a i).1 (w i).1 := by
  rw [radical_f_add]
  unfold f
  abel

private theorem box_strategy {r e : ℕ} {m : Fin r → ℕ} (T : Finset (Fin r))
    (U : (i : Fin r) → Submodule F (V (m i))) (hcard : T.card = e)
    (hiso : ∀ i ∈ T, ∀ u ∈ U i, ∀ v ∈ U i, b u v = 0) :
    ∀ a : X m, ∃ (ask : X m →ₗ[F] (Fin e → F)) (out : (Fin e → F) → (Fin r → F)),
      ∀ w ∈ box T U, out (ask (a + w)) = f (a + w) := by
  classical
  intro a
  let E : {i // i ∈ T} ≃ Fin e := T.equivFin.trans (finCongr hcard)
  let subask : box T U →ₗ[F] (Fin e → F) :=
    { toFun := fun w k => f (a + w.1) (E.symm k).1 - f a (E.symm k).1
      map_add' := by
        intro u v
        funext k
        let i := (E.symm k).1
        change f (a + (u.1 + v.1)) i - f a i =
          (f (a + u.1) i - f a i) + (f (a + v.1) i - f a i)
        simp only [geomDelta]
        have hi : i ∈ T := (E.symm k).2
        have h := hiso i hi (u.1 i).1 ((mem_box T U u.1).mp u.2 |>.1 i hi)
          (v.1 i).1 ((mem_box T U v.1).mp v.2 |>.1 i hi)
        change (u.1 i).2 + (v.1 i).2 + q ((u.1 i).1 + (v.1 i).1) +
          b (a i).1 ((u.1 i).1 + (v.1 i).1) = _
        rw [radical_q_add, radical_b_add_right, h, add_zero]
        ring
      map_smul' := by
        intro c w
        rcases (show ∀ c : F, c = 0 ∨ c = 1 by decide) c with rfl | rfl
        · funext k
          change f (a + ((0 : F) • w.1)) (E.symm k).1 - f a (E.symm k).1 = 0 * _
          simp
        · funext k
          change f (a + ((1 : F) • w.1)) (E.symm k).1 - f a (E.symm k).1 = 1 * _
          simp }
  obtain ⟨ask, hask⟩ := subask.exists_extend
  refine ⟨ask, fun y i => if hi : i ∈ T then f a i + (y - ask a) (E ⟨i, hi⟩) else f a i, ?_⟩
  intro w hw
  funext i
  dsimp only
  split_ifs with hi
  · rw [ask.map_add, add_sub_cancel_left]
    have he : ask w = subask ⟨w, hw⟩ := DFunLike.congr_fun hask ⟨w, hw⟩
    rw [he]
    change f a i + (f (a + w) (E.symm (E ⟨i, hi⟩)).1 -
      f a (E.symm (E ⟨i, hi⟩)).1) = _
    rw [E.symm_apply_apply]
    abel
  · have hzero := ((mem_box T U w).mp hw).2 i hi
    change f a i = (a i).2 + (w i).2 + q ((a i).1 + (w i).1)
    simp [f, hzero]

private lemma extremal_weights {r e : ℕ} {m : Fin r → ℕ} {I T : Finset (Fin r)}
    (hm : ∀ i, 0 < m i) (he : e ≤ r)
    (hmax : ∀ K : Finset (Fin r), K.card = e → (∑ i ∈ K, m i) ≤ ∑ i ∈ I, m i)
    (ht : T.card ≤ e) (hw : (∑ i ∈ I, m i) ≤ ∑ i ∈ T, m i) :
    T.card = e ∧ (∑ i ∈ T, m i) = ∑ i ∈ I, m i := by
  classical
  obtain ⟨K, hTK, _, hk⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ T) ht (by simpa using he : e ≤ (Finset.univ : Finset (Fin r)).card)
  have hkW := hmax K hk
  have hTKsum : (∑ i ∈ T, m i) ≤ ∑ i ∈ K, m i :=
    Finset.sum_le_sum_of_subset_of_nonneg hTK (fun _ _ _ => Nat.zero_le _)
  refine ⟨?_, le_antisymm (hTKsum.trans hkW) hw⟩
  by_contra hn
  have hne : T ≠ K := fun h => hn (h ▸ hk)
  obtain ⟨i, hiK, hiT⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hTK hne)
  have hlt : (∑ i ∈ T, m i) < ∑ i ∈ K, m i :=
    Finset.sum_lt_sum_of_subset hTK hiK hiT (hm i) (fun _ _ _ => Nat.zero_le _)
  omega

private lemma classify {r e : ℕ} {m : Fin r → ℕ} {I : Finset (Fin r)}
    (hm : ∀ i, 0 < m i) (he : e ≤ r)
    (hmax : ∀ K : Finset (Fin r), K.card = e → (∑ i ∈ K, m i) ≤ ∑ i ∈ I, m i)
    (S : Submodule F (X m)) (hS : Module.finrank F S = e + ∑ i ∈ I, m i)
    (h : ∀ a : X m, ∃ (ask : X m →ₗ[F] (Fin e → F)) (out : (Fin e → F) → (Fin r → F)),
      ∀ w ∈ S, out (ask (a + w)) = f (a + w)) :
    ∃ (T : Finset (Fin r)) (U : (i : Fin r) → Submodule F (V (m i))),
      T.card = e ∧ (∑ i ∈ T, m i) = ∑ i ∈ I, m i ∧
      (∀ i ∈ T, Module.finrank F (U i) = m i ∧
        ∀ u ∈ U i, ∀ v ∈ U i, b u v = 0) ∧ S = box T U := by
  classical
  let R := rad S
  have hbase : Module.finrank F S ≤ e + Module.finrank F R := by
    have hh := row_rank_bound S h (fun i => (0 : V (m i)))
    change Module.finrank F S + _ ≤ e + Module.finrank F R at hh
    omega
  let p := e + Module.finrank F R - Module.finrank F S
  let : Finite (Module.Dual F R) :=
    Finite.of_injective (fun g : Module.Dual F R => (g : R → F)) DFunLike.coe_injective
  let : Fintype (Module.Dual F R) := Fintype.ofFinite _
  let A (i : Fin r) : Finset (Module.Dual F R) := Finset.univ.image (row S i)
  have hA (i : Fin r) : (A i).Nonempty :=
    ⟨row S i 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  have hchoices (g : Fin r → Module.Dual F R) (hg : ∀ i, g i ∈ A i) :
      Module.finrank F (Submodule.span F (Set.range g)) ≤ p := by
    have hv (i : Fin r) : ∃ a : V (m i), row S i a = g i := by
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (hg i)
      exact ⟨a, ha⟩
    choose a ha using hv
    have hga : (fun i => row S i (a i)) = g := funext ha
    have hb := row_rank_bound S h a
    rw [hga] at hb
    change Module.finrank F S + Module.finrank F (Submodule.span F (Set.range g)) ≤
      e + Module.finrank F R at hb
    dsimp [p]
    omega
  obtain ⟨J, hJ⟩ := rado_deficit A hA p hchoices
  let T : Finset (Fin r) := Jᶜ
  let W := Submodule.span F (un A J)
  let C := W.dualCoannihilator.map R.subtype
  have hCdim : Module.finrank F C = Module.finrank F W.dualCoannihilator :=
    Submodule.finrank_map_subtype_eq _ _
  have hTcard : T.card = r - J.card := by simp [T, Finset.card_compl]
  have hcodim := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  have hmain : Module.finrank F S + T.card ≤ e + Module.finrank F C := by
    change Module.finrank F W + (Fintype.card (Fin r) - J.card) ≤ p at hJ
    rw [Fintype.card_fin, ← hTcard] at hJ
    dsimp [p] at hJ
    omega
  have hCR : C ≤ R := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hCS : C ≤ S := hCR.trans (rad_le S)
  have hsupp {x : X m} (hx : x ∈ C) (i : Fin r) (hi : i ∉ T) : x i = 0 := by
    obtain ⟨z, hz, rfl⟩ := hx
    have hiJ : i ∈ J := by simpa [T] using hi
    apply (row_all_zero_iff S i z).mp
    intro a
    apply (Submodule.mem_dualCoannihilator z).mp hz
    apply Submodule.subset_span
    simp only [un, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨i, hiJ, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  let coord (i : Fin r) : X m →ₗ[F] V (m i) :=
    (LinearMap.fst F (V (m i)) F).comp (LinearMap.proj i)
  let U (i : Fin r) : Submodule F (V (m i)) := C.map (coord i)
  have hiso (i : Fin r) : ∀ u ∈ U i, ∀ v ∈ U i, b u v = 0 := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact rad_b_zero (hCR hx) (hCS hy) i
  have hU (i : Fin r) : Module.finrank F (U i) ≤ m i := iso_rank_le (U i) (hiso i)
  have hCB : C ≤ box T U := by
    intro x hx
    exact (mem_box T U x).mpr ⟨fun i _ => ⟨x, hx, rfl⟩, hsupp hx⟩
  have hdimCS := Submodule.finrank_mono hCS
  have hdimCB := Submodule.finrank_mono hCB
  have hbox := finrank_box T U
  have hsum : (∑ i ∈ T, Module.finrank F (U i)) ≤ ∑ i ∈ T, m i :=
    Finset.sum_le_sum fun i _ => hU i
  have hcard : T.card ≤ e := by omega
  have hweight : (∑ i ∈ I, m i) ≤ ∑ i ∈ T, m i := by omega
  obtain ⟨hc, hw⟩ := extremal_weights hm he hmax hcard hweight
  have hSC : S = C := (Submodule.eq_of_le_of_finrank_eq hCS (by omega)).symm
  have hCbox : C = box T U := Submodule.eq_of_le_of_finrank_eq hCB (by omega)
  refine ⟨T, U, hc, hw, fun i hi => ⟨?_, hiso i⟩, hSC.trans hCbox⟩
  by_contra hn
  have hlt : Module.finrank F (U i) < m i := lt_of_le_of_ne (hU i) hn
  have hsumlt : (∑ j ∈ T, Module.finrank F (U j)) < ∑ j ∈ T, m j :=
    Finset.sum_lt_sum (fun j _ => hU j) ⟨i, hi, hlt⟩
  omega

end PEqualNP.Outside.L_pcx_429

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_pcx_429 :
∀ (r : ℕ) (m : Fin r → ℕ) (_ : ∀ i, 0 < m i) (e : ℕ) (_ : e ≤ r),
  let F := ZMod 2
  let V := fun i : Fin r => (Fin (m i) → F) × (Fin (m i) → F)
  let X := (i : Fin r) → V i × F
  let Y := Fin r → F
  let f := fun (x : X) (i : Fin r) =>
    (x i).2 + ∑ j : Fin (m i), (x i).1.1 j * (x i).1.2 j
  let B := fun (i : Fin r) (u v : V i) =>
    ∑ j : Fin (m i), (u.1 j*v.2 j + u.2 j*v.1 j)
  ∀ (I : Finset (Fin r)) (_ : I.card = e)
    (_ : ∀ K : Finset (Fin r), K.card = e → (∑ i ∈ K, m i) ≤ ∑ i ∈ I, m i)
    (S : Submodule F X) (_ : Module.finrank F S = e + ∑ i ∈ I, m i),
    (∀ a : X, ∃ (ask : X →ₗ[F] (Fin e → F)) (out : (Fin e → F) → Y),
      ∀ w ∈ S, out (ask (a+w)) = f (a+w)) ↔
    ∃ (T : Finset (Fin r)) (U : (i : Fin r) → Submodule F (V i)),
      T.card = e ∧ (∑ i ∈ T, m i) = ∑ i ∈ I, m i ∧
      (∀ i ∈ T, Module.finrank F (U i) = m i ∧
        ∀ u ∈ U i, ∀ v ∈ U i, B i u v = 0) ∧
      ∀ w : X, w ∈ S ↔
        (∀ i ∈ T, (w i).1 ∈ U i) ∧ (∀ i : Fin r, i ∉ T → w i = 0) := by
  classical
  dsimp only
  intro r m hm e he I _ hmax S hdim
  constructor
  · intro h
    obtain ⟨T, U, ht, hw, hU, hS⟩ := L_pcx_429.classify hm he hmax S hdim h
    refine ⟨T, U, ht, hw, hU, ?_⟩
    intro x
    rw [hS]
    exact L_pcx_429.mem_box T U x
  · rintro ⟨T, U, ht, _, hU, hS⟩
    have hEq : S = L_pcx_429.box T U := by
      ext x
      exact (hS x).trans (L_pcx_429.mem_box T U x).symm
    subst S
    exact L_pcx_429.box_strategy T U ht (fun i hi => (hU i hi).2)
