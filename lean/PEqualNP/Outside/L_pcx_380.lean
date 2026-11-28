import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_380

private abbrev Vec (n : ℕ) := Fin n → ZMod 2
private abbrev Dual (n : ℕ) := Vec n →ₗ[ZMod 2] ZMod 2

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  match a with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

private lemma zmod2_eq_iff_add_eq_zero (a b : ZMod 2) : a = b ↔ a + b = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private def Ddual {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) : Dual n →ₗ[ZMod 2] Dual n where
  toFun a := a.comp T.toLinearMap + a
  map_add' a₁ a₂ := by ext x; simp; ring
  map_smul' c a := by ext x; simp

private lemma shift_eq_map {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (S : Submodule (ZMod 2) (Dual n)) :
    Submodule.span (ZMod 2) (Set.image (fun a : Dual n => a.comp T.toLinearMap + a) (S : Set (Dual n))) =
      S.map (Ddual T) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨a, ha, rfl⟩

private def Ann {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) : Submodule (ZMod 2) (Vec n) :=
  { carrier := {v | ∀ φ ∈ M, φ v = 0}, zero_mem' := fun φ _ => map_zero φ, add_mem' := fun {u v} hu hv φ hφ => by rw [map_add, hu φ hφ, hv φ hφ, add_zero], smul_mem' := fun c {v} hv φ hφ => by rw [map_smul, hv φ hφ, smul_zero] }

private lemma mem_Ann_iff {n : ℕ} {M : Submodule (ZMod 2) (Dual n)} {v : Vec n} :
    v ∈ Ann M ↔ ∀ φ ∈ M, φ v = 0 := Iff.rfl

private lemma mem_Ann_sup {n : ℕ} {M₁ M₂ : Submodule (ZMod 2) (Dual n)} {v : Vec n} :
    v ∈ Ann (M₁ ⊔ M₂) ↔ v ∈ Ann M₁ ∧ v ∈ Ann M₂ := by
  constructor
  · intro h
    exact ⟨fun φ hφ => h φ (Submodule.mem_sup_left hφ),
      fun φ hφ => h φ (Submodule.mem_sup_right hφ)⟩
  · rintro ⟨h1, h2⟩ φ hφ
    rcases Submodule.mem_sup.mp hφ with ⟨φ₁, hφ₁, φ₂, hφ₂, rfl⟩
    rw [LinearMap.add_apply, h1 φ₁ hφ₁, h2 φ₂ hφ₂, add_zero]

private lemma mem_Ann_span {n : ℕ} {s : Set (Dual n)} {v : Vec n} :
    v ∈ Ann (Submodule.span (ZMod 2) s) ↔ ∀ φ ∈ s, φ v = 0 := by
  constructor
  · intro h φ hφ; exact h φ (Submodule.subset_span hφ)
  · intro h φ hφ
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
    · intro ψ hψ; exact h ψ hψ
    · simp
    · intro ψ₁ ψ₂ _ _ h1 h2; simp [h1, h2]
    · intro c ψ _ h1; simp [h1]

private lemma mem_Ann_map_Ddual {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    {M : Submodule (ZMod 2) (Dual n)} {v : Vec n} :
    v ∈ Ann (M.map (Ddual T)) ↔ ∀ φ ∈ M, Ddual T φ v = 0 := by
  constructor
  · intro h φ hφ; exact h (Ddual T φ) ⟨φ, hφ, rfl⟩
  · intro h _ hψ
    rcases hψ with ⟨φ, hφ, rfl⟩
    exact h φ hφ

private lemma Ann_top_eq_bot {n : ℕ} :
    Ann (⊤ : Submodule (ZMod 2) (Dual n)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  ext i
  exact hv (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) i) Submodule.mem_top

private lemma dual_eq_sum_proj {n : ℕ} (φ : Dual n) :
    φ = ∑ i : Fin n, φ (Pi.single i (1 : ZMod 2)) •
      LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) i := by
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i : Fin n, x i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, map_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private def evalSub {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Vec n →ₗ[ZMod 2] (M →ₗ[ZMod 2] ZMod 2) where
  toFun v :=
    { toFun := fun φ => φ.1 v
      map_add' := fun φ₁ φ₂ => rfl
      map_smul' := fun c φ => rfl }
  map_add' u v := by ext φ; exact map_add φ.1 u v
  map_smul' c v := by ext φ; exact map_smul φ.1 c v

private lemma evalSub_ker {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    LinearMap.ker (evalSub M) = Ann M := by
  ext v
  simp only [LinearMap.mem_ker, mem_Ann_iff]
  constructor
  · intro h φ hφ
    have := LinearMap.congr_fun h ⟨φ, hφ⟩
    exact this
  · intro h
    ext ⟨φ, hφ⟩
    exact h φ hφ

private lemma evalSub_surjective {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Function.Surjective (evalSub M) := by
  intro ψ
  rcases Submodule.exists_isCompl M with ⟨N, hMN⟩
  let projM : Dual n →ₗ[ZMod 2] M := Submodule.linearProjOfIsCompl M N hMN
  let Ψ : Dual n →ₗ[ZMod 2] ZMod 2 := ψ.comp projM
  let v : Vec n := fun i => Ψ (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) i)
  refine ⟨v, ?_⟩
  ext ⟨φ, hφ⟩
  change φ v = ψ ⟨φ, hφ⟩
  have hΨφ : Ψ φ = ψ ⟨φ, hφ⟩ := by
    change ψ (Submodule.linearProjOfIsCompl M N hMN φ) = ψ ⟨φ, hφ⟩
    congr 1
    exact Submodule.linearProjOfIsCompl_apply_left hMN ⟨φ, hφ⟩
  rw [← hΨφ]
  conv_rhs => rw [dual_eq_sum_proj φ, map_sum]
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  dsimp only [v]
  ring

private lemma finrank_Ann_add_finrank {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Module.finrank (ZMod 2) (Ann M) + Module.finrank (ZMod 2) M = n := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (evalSub M)
  rw [LinearMap.range_eq_top.mpr (evalSub_surjective M), evalSub_ker M,
    finrank_top, Module.finrank_fin_fun] at hrk
  letI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  have hdual : Module.finrank (ZMod 2) (M →ₗ[ZMod 2] ZMod 2) = Module.finrank (ZMod 2) M := by
    rw [Module.finrank_eq_card_basis (Module.finBasis (ZMod 2) M).dualBasis, Fintype.card_fin]
  omega

private lemma finrank_dual_le {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Module.finrank (ZMod 2) M ≤ n := by
  have := finrank_Ann_add_finrank M
  omega

open Classical in
private lemma card_coset_Ann {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) (x₀ : Vec n) :
    (Finset.univ.filter (fun x : Vec n => x - x₀ ∈ Ann M)).card =
      2 ^ (n - Module.finrank (ZMod 2) M) := by
  have hbij : (Finset.univ.filter (fun x : Vec n => x - x₀ ∈ Ann M)).card =
      Fintype.card (Ann M) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun x hx => ⟨x - x₀, (Finset.mem_filter.mp hx).2⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ _ x₂ _ heq => by
        have h : x₁ - x₀ = x₂ - x₀ := congrArg Subtype.val heq
        exact sub_left_inj.mp h)
      (fun v _ => ⟨v.1 + x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [v.2]⟩,
        by ext; simp⟩)
  rw [hbij, Module.card_eq_pow_finrank (K := ZMod 2) (V := Ann M), ZMod.card 2]
  have hsum := finrank_Ann_add_finrank M
  congr 1
  omega

private def step {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (hist : List (Fin w → ZMod 2)) :
    List (Fin w → ZMod 2) :=
  hist ++ [fun i : Fin w => (ask hist i).1 word + (ask hist i).2.1 * layer + (ask hist i).2.2]

private def tr {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) : ℕ → List (Fin w → ZMod 2)
  | 0 => []
  | j + 1 => step ask layer word (tr ask layer word j)

private lemma tr_eq_foldl {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (s : ℕ) :
    (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
      hist ++ [fun i : Fin w => (ask hist i).1 word + (ask hist i).2.1 * layer + (ask hist i).2.2]) [] =
      tr ask layer word s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [List.range_succ, List.foldl_concat, ih]
    rfl

private lemma tr_length {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (j : ℕ) :
    (tr ask layer word j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [tr, step, ih]

private lemma tr_take {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (j : ℕ) :
    (tr ask layer word (j + 1)).take j = tr ask layer word j := by
  change (tr ask layer word j ++ [_]).take j = tr ask layer word j
  rw [List.take_left' (tr_length ask layer word j)]

private lemma tr_take_le {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) {r j : ℕ} (hrj : r ≤ j) :
    (tr ask layer word j).take r = tr ask layer word r := by
  induction j with
  | zero =>
    have hr0 : r = 0 := by omega
    subst hr0; rfl
  | succ j ih =>
    by_cases h : r = j + 1
    · subst h; rw [List.take_of_length_le (by rw [tr_length])]
    · have hrle : r ≤ j := by omega
      rw [← ih hrle, ← tr_take ask layer word j, List.take_take, Nat.min_eq_left hrle]

private lemma tr_succ_eq_iff {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (word : Vec n) (j : ℕ)
    (h : List (Fin w → ZMod 2)) (hlen : h.length = j) (y : Fin w → ZMod 2) :
    tr ask layer word (j + 1) = h ++ [y] ↔
      tr ask layer word j = h ∧
      (fun i : Fin w => (ask h i).1 word + (ask h i).2.1 * layer + (ask h i).2.2) = y := by
  change tr ask layer word j ++
      [fun i : Fin w => (ask (tr ask layer word j) i).1 word +
        (ask (tr ask layer word j) i).2.1 * layer + (ask (tr ask layer word j) i).2.2] =
      h ++ [y] ↔ _
  constructor
  · intro heq
    have h1 : tr ask layer word j = h := by
      have ht := congrArg (List.take j) heq
      rw [List.take_left' (tr_length ask layer word j), List.take_left' hlen] at ht
      exact ht
    rw [h1] at heq
    have h2 : [fun i : Fin w => (ask h i).1 word + (ask h i).2.1 * layer + (ask h i).2.2] = [y] :=
      List.append_cancel_left heq
    exact ⟨h1, (List.cons.inj h2).1⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

private lemma layer_agree_iff {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (a : Dual n) (c₁ c₂ : ZMod 2) (x : Vec n) :
    (a x + c₁ * 0 + c₂ = a (T x + b) + c₁ * 1 + c₂) ↔
      Ddual T a x = a b + c₁ := by
  simp only [mul_zero, add_zero, mul_one, map_add, add_left_inj]
  change a x = a (T x) + a b + c₁ ↔ a (T x) + a x = a b + c₁
  rw [zmod2_eq_iff_add_eq_zero (a x), zmod2_eq_iff_add_eq_zero (a (T x) + a x)]
  have hring : a x + (a (T x) + a b + c₁) = a (T x) + a x + (a b + c₁) := by ring
  rw [hring]

private def Hists (w : ℕ) : ℕ → Finset (List (Fin w → ZMod 2))
  | 0 => {[]}
  | j + 1 => (Hists w j).biUnion (fun h => Finset.univ.image (fun y : Fin w → ZMod 2 => h ++ [y]))

private lemma mem_Hists_iff {w j : ℕ} {h : List (Fin w → ZMod 2)} :
    h ∈ Hists w j ↔ h.length = j := by
  induction j generalizing h with
  | zero =>
    simp [Hists]
  | succ j ih =>
    simp only [Hists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, ih]
    constructor
    · rintro ⟨h', hh', y, rfl⟩
      simp [hh']
    · intro hlen
      have hne : h ≠ [] := by intro h0; subst h0; simp at hlen
      refine ⟨h.dropLast, ?_, h.getLast hne, List.dropLast_append_getLast hne⟩
      simp [hlen]

private lemma sum_Hists_succ {w j : ℕ} (f : List (Fin w → ZMod 2) → ℕ) :
    ∑ h' ∈ Hists w (j + 1), f h' =
      ∑ h ∈ Hists w j, ∑ y : Fin w → ZMod 2, f (h ++ [y]) := by
  change ∑ h' ∈ (Hists w j).biUnion (fun h => Finset.univ.image (fun y => h ++ [y])), f h' = _
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [Finset.sum_image]
    intro y₁ _ y₂ _ heq
    exact (List.cons.inj (List.append_cancel_left heq)).1
  · intro h₁ hh₁ h₂ hh₂ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases Finset.mem_image.mp hx₁ with ⟨y₁, _, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨y₂, _, heq⟩
    have hl1 : h₁.length = j := mem_Hists_iff.mp hh₁
    have hl2 : h₂.length = j := mem_Hists_iff.mp hh₂
    have ht := congrArg (List.take j) heq
    rw [List.take_left' hl1, List.take_left' hl2] at ht
    exact hne ht.symm

private def roundSpace {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) : Submodule (ZMod 2) (Dual n) :=
  Submodule.span (ZMod 2) (Set.range (fun i : Fin w => (ask h i).1))

private def histFlag {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) : ℕ → Submodule (ZMod 2) (Dual n)
  | 0 => ⊥
  | j + 1 => histFlag ask h j ⊔ roundSpace ask (h.take j)

private lemma histFlag_eq_of_take {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h₁ h₂ : List (Fin w → ZMod 2)) (j : ℕ) (ht : h₁.take j = h₂.take j) :
    histFlag ask h₁ j = histFlag ask h₂ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hprev : h₁.take j = h₂.take j := by
      have := congrArg (List.take j) ht
      rwa [List.take_take, List.take_take, Nat.min_eq_left (Nat.le_succ j)] at this
    simp only [histFlag, ih hprev, hprev]

private lemma histFlag_append {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) (y : Fin w → ZMod 2) (j : ℕ) (hlen : h.length = j) :
    histFlag ask (h ++ [y]) (j + 1) = histFlag ask h j ⊔ roundSpace ask h := by
  simp only [histFlag]
  have ht : (h ++ [y]).take j = h := List.take_left' hlen
  have htake : (h ++ [y]).take j = h.take j := by
    rw [ht, List.take_of_length_le (le_of_eq hlen)]
  rw [histFlag_eq_of_take ask (h ++ [y]) h j htake, ht]

private noncomputable def stepCost {n : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (A B : Submodule (ZMod 2) (Dual n)) : ℕ :=
  let base := A ⊔ A.map (Ddual T)
  Module.finrank (ZMod 2) (base ⊔ B.map (Ddual T) : Submodule (ZMod 2) (Dual n)) -
    Module.finrank (ZMod 2) base

private noncomputable def histCost {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) : ℕ → ℕ
  | 0 => 0
  | j + 1 => histCost T ask h j +
      stepCost T (histFlag ask h j) (histFlag ask h (j + 1))

private lemma histCost_eq_of_take {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h₁ h₂ : List (Fin w → ZMod 2)) (j : ℕ) (ht : h₁.take j = h₂.take j) :
    histCost T ask h₁ j = histCost T ask h₂ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hprev : h₁.take j = h₂.take j := by
      have := congrArg (List.take j) ht
      rwa [List.take_take, List.take_take, Nat.min_eq_left (Nat.le_succ j)] at this
    simp only [histCost, ih hprev, histFlag_eq_of_take ask h₁ h₂ j hprev,
      histFlag_eq_of_take ask h₁ h₂ (j + 1) ht]

private lemma histCost_eq_range_sum {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (h : List (Fin w → ZMod 2)) (s : ℕ) :
    histCost T ask h s =
      (Finset.range s).sum (fun j => stepCost T (histFlag ask h j) (histFlag ask h (j + 1))) := by
  induction s with
  | zero => simp [histCost]
  | succ s ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

private lemma surv_coset_iff {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (j : ℕ) (h : List (Fin w → ZMod 2)) (hlen : h.length = j)
    (x₀ : Vec n) (hx₀ : tr ask 0 x₀ j = h ∧ tr ask 1 (T x₀ + b) j = h) :
    ∀ x : Vec n, (tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h) ↔
      x - x₀ ∈ Ann (histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) := by
  induction j generalizing h with
  | zero =>
    have hnil : h = [] := List.eq_nil_of_length_eq_zero hlen
    subst hnil
    intro x
    simp [tr, histFlag, Ann]
  | succ j ih =>
    have hne : h ≠ [] := by intro h0; subst h0; simp at hlen
    set h' := h.dropLast
    set y := h.getLast hne
    have hcat : h = h' ++ [y] := (List.dropLast_append_getLast hne).symm
    have h'len : h'.length = j := by simp [h', hlen]
    have hx₀_split : (tr ask 0 x₀ j = h' ∧
        (fun i => (ask h' i).1 x₀ + (ask h' i).2.1 * 0 + (ask h' i).2.2) = y) ∧
        (tr ask 1 (T x₀ + b) j = h' ∧
        (fun i => (ask h' i).1 (T x₀ + b) + (ask h' i).2.1 * 1 + (ask h' i).2.2) = y) := by
      rw [hcat] at hx₀
      exact ⟨(tr_succ_eq_iff ask 0 x₀ j h' h'len y).mp hx₀.1,
        (tr_succ_eq_iff ask 1 (T x₀ + b) j h' h'len y).mp hx₀.2⟩
    have hx₀_prev : tr ask 0 x₀ j = h' ∧ tr ask 1 (T x₀ + b) j = h' :=
      ⟨hx₀_split.1.1, hx₀_split.2.1⟩
    have hx₀_agree : ∀ i : Fin w, Ddual T (ask h' i).1 x₀ = (ask h' i).1 b + (ask h' i).2.1 := by
      intro i
      rw [← layer_agree_iff T b (ask h' i).1 (ask h' i).2.1 (ask h' i).2.2 x₀]
      have e1 := congrFun hx₀_split.1.2 i
      have e2 := congrFun hx₀_split.2.2 i
      exact e1.trans e2.symm
    have hflag_eq : histFlag ask h (j + 1) = histFlag ask h' j ⊔ roundSpace ask h' := by
      rw [hcat]
      exact histFlag_append ask h' y j h'len
    intro x
    rw [hflag_eq, Submodule.map_sup]
    have hsup_rearr : (histFlag ask h' j ⊔ roundSpace ask h') ⊔
        ((histFlag ask h' j).map (Ddual T) ⊔ (roundSpace ask h').map (Ddual T)) =
        (histFlag ask h' j ⊔ (histFlag ask h' j).map (Ddual T)) ⊔
        (roundSpace ask h' ⊔ (roundSpace ask h').map (Ddual T)) := by
      ac_rfl
    rw [hsup_rearr, mem_Ann_sup, ← ih h' h'len hx₀_prev x, hcat,
      tr_succ_eq_iff ask 0 x j h' h'len y, tr_succ_eq_iff ask 1 (T x + b) j h' h'len y]
    rw [mem_Ann_sup, roundSpace, mem_Ann_span, mem_Ann_map_Ddual]
    constructor
    · rintro ⟨⟨h0p, h0y⟩, ⟨h1p, h1y⟩⟩
      refine ⟨⟨h0p, h1p⟩, ?_, ?_⟩
      · rintro _ ⟨i, rfl⟩
        have e1 := congrFun h0y i
        have e2 := congrFun hx₀_split.1.2 i
        have hax : (ask h' i).1 x = (ask h' i).1 x₀ := by
          simp only [mul_zero, add_zero] at e1 e2
          exact add_right_cancel (e1.trans e2.symm)
        rw [map_sub, hax, sub_self]
      · intro φ hφ
        have hker : ∀ i : Fin w, Ddual T (ask h' i).1 (x - x₀) = 0 := by
          intro i
          have hax_ag : Ddual T (ask h' i).1 x = (ask h' i).1 b + (ask h' i).2.1 := by
            rw [← layer_agree_iff T b (ask h' i).1 (ask h' i).2.1 (ask h' i).2.2 x]
            exact (congrFun h0y i).trans (congrFun h1y i).symm
          rw [map_sub, hax_ag, hx₀_agree i, sub_self]
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
        · rintro _ ⟨i, rfl⟩; exact hker i
        · simp
        · intro ψ₁ ψ₂ _ _ h1 h2; simp [h1, h2]
        · intro c ψ _ h1; simp [h1]
    · rintro ⟨⟨h0p, h1p⟩, hR0, hRD⟩
      have h0y : (fun i => (ask h' i).1 x + (ask h' i).2.1 * 0 + (ask h' i).2.2) = y := by
        ext i
        have hsub : (ask h' i).1 (x - x₀) = 0 := hR0 _ ⟨i, rfl⟩
        have hax : (ask h' i).1 x = (ask h' i).1 x₀ := sub_eq_zero.mp (by rwa [map_sub] at hsub)
        rw [hax]
        exact congrFun hx₀_split.1.2 i
      have h1y : (fun i => (ask h' i).1 (T x + b) + (ask h' i).2.1 * 1 + (ask h' i).2.2) = y := by
        ext i
        have hsub : Ddual T (ask h' i).1 (x - x₀) = 0 :=
          hRD (ask h' i).1 (Submodule.subset_span ⟨i, rfl⟩)
        have hd : Ddual T (ask h' i).1 x = (ask h' i).1 b + (ask h' i).2.1 := by
          rw [← hx₀_agree i]
          exact sub_eq_zero.mp (by rwa [map_sub] at hsub)
        have hag := (layer_agree_iff T b (ask h' i).1 (ask h' i).2.1 (ask h' i).2.2 x).mpr hd
        rw [← hag]
        exact congrFun h0y i
      exact ⟨⟨h0p, h0y⟩, ⟨h1p, h1y⟩⟩

private lemma agree_next_coset_iff {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (j : ℕ) (h : List (Fin w → ZMod 2)) (hlen : h.length = j)
    (x₁ : Vec n)
    (hx₁ : tr ask 0 x₁ j = h ∧ tr ask 1 (T x₁ + b) j = h ∧
      tr ask 0 x₁ j = tr ask 0 x₁ j ∧
      (fun i : Fin w => (ask h i).1 x₁ + (ask h i).2.1 * 0 + (ask h i).2.2) =
      (fun i : Fin w => (ask h i).1 (T x₁ + b) + (ask h i).2.1 * 1 + (ask h i).2.2)) :
    ∀ x : Vec n,
      (tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h ∧
        (fun i : Fin w => (ask h i).1 x + (ask h i).2.1 * 0 + (ask h i).2.2) =
        (fun i : Fin w => (ask h i).1 (T x + b) + (ask h i).2.1 * 1 + (ask h i).2.2)) ↔
      x - x₁ ∈ Ann ((histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) ⊔
        (roundSpace ask h).map (Ddual T)) := by
  have hx₁_ag : ∀ i : Fin w, Ddual T (ask h i).1 x₁ = (ask h i).1 b + (ask h i).2.1 := by
    intro i
    rw [← layer_agree_iff T b (ask h i).1 (ask h i).2.1 (ask h i).2.2 x₁]
    exact congrFun hx₁.2.2.2 i
  intro x
  rw [mem_Ann_sup, ← surv_coset_iff T b ask j h hlen x₁ ⟨hx₁.1, hx₁.2.1⟩ x, mem_Ann_map_Ddual]
  constructor
  · rintro ⟨h0, h1, hag⟩
    refine ⟨⟨h0, h1⟩, ?_⟩
    intro φ hφ
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
    · rintro _ ⟨i, rfl⟩
      have hd : Ddual T (ask h i).1 x = (ask h i).1 b + (ask h i).2.1 := by
        rw [← layer_agree_iff T b (ask h i).1 (ask h i).2.1 (ask h i).2.2 x]
        exact congrFun hag i
      rw [map_sub, hd, hx₁_ag i, sub_self]
    · simp
    · intro ψ₁ ψ₂ _ _ h1' h2'; simp [h1', h2']
    · intro c ψ _ h1'; simp [h1']
  · rintro ⟨⟨h0, h1⟩, hRD⟩
    refine ⟨h0, h1, ?_⟩
    ext i
    rw [layer_agree_iff T b (ask h i).1 (ask h i).2.1 (ask h i).2.2 x]
    have hsub : Ddual T (ask h i).1 (x - x₁) = 0 :=
      hRD (ask h i).1 (Submodule.subset_span ⟨i, rfl⟩)
    rw [← hx₁_ag i]
    exact sub_eq_zero.mp (by rwa [map_sub] at hsub)

open Classical in
private lemma children_card_mul_pow_le {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (j : ℕ) (h : List (Fin w → ZMod 2)) (hlen : h.length = j) :
    (∑ y : Fin w → ZMod 2,
      (Finset.univ.filter (fun x : Vec n =>
        tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
      2 ^ (stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h)) ≤
    (Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)).card := by
  set Surv := Finset.univ.filter (fun x : Vec n =>
    tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h ∧
    (fun i : Fin w => (ask h i).1 x + (ask h i).2.1 * 0 + (ask h i).2.2) =
    (fun i : Fin w => (ask h i).1 (T x + b) + (ask h i).2.1 * 1 + (ask h i).2.2))
  set Parent := Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)
  have hsum_eq : ∑ y : Fin w → ZMod 2,
      (Finset.univ.filter (fun x : Vec n =>
        tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card = Surv.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Surv, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
        tr_succ_eq_iff ask 0 x j h hlen, tr_succ_eq_iff ask 1 (T x + b) j h hlen]
      constructor
      · rintro ⟨y, ⟨h0, hy0⟩, ⟨h1, hy1⟩⟩
        exact ⟨h0, h1, hy0.trans hy1.symm⟩
      · rintro ⟨h0, h1, hag⟩
        exact ⟨_, ⟨h0, rfl⟩, ⟨h1, hag.symm⟩⟩
    · intro y₁ _ y₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have h1 := ((tr_succ_eq_iff ask 0 x j h hlen y₁).mp (Finset.mem_filter.mp hx₁).2.1).2
      have h2 := ((tr_succ_eq_iff ask 0 x j h hlen y₂).mp (Finset.mem_filter.mp hx₂).2.1).2
      exact hne (h1.symm.trans h2)
  rw [hsum_eq]
  by_cases hne : Surv.Nonempty
  · rcases hne with ⟨x₁, hx₁⟩
    have hx₁' := (Finset.mem_filter.mp hx₁).2
    have hSurv_eq : Surv = Finset.univ.filter (fun x : Vec n =>
        x - x₁ ∈ Ann ((histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) ⊔
          (roundSpace ask h).map (Ddual T))) := by
      ext x
      simp only [Surv, Finset.mem_filter, Finset.mem_univ, true_and]
      exact agree_next_coset_iff T b ask j h hlen x₁ ⟨hx₁'.1, hx₁'.2.1, rfl, hx₁'.2.2⟩ x
    have hParent_eq : Parent = Finset.univ.filter (fun x : Vec n =>
        x - x₁ ∈ Ann (histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T))) := by
      ext x
      simp only [Parent, Finset.mem_filter, Finset.mem_univ, true_and]
      exact surv_coset_iff T b ask j h hlen x₁ ⟨hx₁'.1, hx₁'.2.1⟩ x
    rw [hSurv_eq, hParent_eq, card_coset_Ann, card_coset_Ann]
    set base := histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)
    have hstep_eq : stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h) =
        Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) -
          Module.finrank (ZMod 2) base := by
      unfold stepCost
      dsimp only
      have heq : base ⊔ (histFlag ask h j ⊔ roundSpace ask h).map (Ddual T) =
          base ⊔ (roundSpace ask h).map (Ddual T) := by
        rw [Submodule.map_sup]
        change (histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) ⊔
            ((histFlag ask h j).map (Ddual T) ⊔ (roundSpace ask h).map (Ddual T)) =
            (histFlag ask h j ⊔ (histFlag ask h j).map (Ddual T)) ⊔ (roundSpace ask h).map (Ddual T)
        apply le_antisymm
        · refine sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right))
            (sup_le (le_sup_of_le_left le_sup_right) le_sup_right)
        · exact sup_le le_sup_left (le_sup_of_le_right le_sup_right)
      rw [heq]
    rw [hstep_eq, ← pow_add]
    have hle1 : Module.finrank (ZMod 2) base ≤
        Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) :=
      Submodule.finrank_mono le_sup_left
    have hle2 : Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) ≤ n :=
      finrank_dual_le _
    have hexp : n - Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) +
        (Module.finrank (ZMod 2) (base ⊔ (roundSpace ask h).map (Ddual T) : Submodule (ZMod 2) (Dual n)) -
          Module.finrank (ZMod 2) base) = n - Module.finrank (ZMod 2) base := by omega
    rw [hexp]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, zero_mul]
    exact Nat.zero_le _

open Classical in
private lemma weighted_sum_le {n w : ℕ} (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2) (j : ℕ) :
    ∑ h ∈ Hists w j,
      (Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)).card *
        2 ^ (histCost T ask h j) ≤ 2 ^ n := by
  induction j with
  | zero =>
    simp only [Hists, Finset.sum_singleton, histCost, pow_zero, mul_one, tr, true_and,
      Finset.filter_true, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
      ZMod.card 2, Finset.prod_const]
    exact le_rfl
  | succ j ih =>
    rw [sum_Hists_succ]
    refine le_trans ?_ ih
    refine Finset.sum_le_sum (fun h hh => ?_)
    have hlen : h.length = j := mem_Hists_iff.mp hh
    have hcost : ∀ y : Fin w → ZMod 2,
        histCost T ask (h ++ [y]) (j + 1) =
          histCost T ask h j + stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h) := by
      intro y
      simp only [histCost]
      have htake : (h ++ [y]).take j = h.take j := by
        rw [List.take_left' hlen, List.take_of_length_le (le_of_eq hlen)]
      rw [histCost_eq_of_take T ask (h ++ [y]) h j htake,
        histFlag_eq_of_take ask (h ++ [y]) h j htake,
        histFlag_append ask h y j hlen]
    calc ∑ y : Fin w → ZMod 2,
          (Finset.univ.filter (fun x : Vec n =>
            tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card *
          2 ^ histCost T ask (h ++ [y]) (j + 1)
        = ∑ y : Fin w → ZMod 2,
          (Finset.univ.filter (fun x : Vec n =>
            tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card *
          (2 ^ stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h) *
            2 ^ histCost T ask h j) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hcost y, pow_add, mul_comm (2 ^ histCost T ask h j)]
      _ = ((∑ y : Fin w → ZMod 2,
            (Finset.univ.filter (fun x : Vec n =>
              tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
            2 ^ stepCost T (histFlag ask h j) (histFlag ask h j ⊔ roundSpace ask h)) *
          2 ^ histCost T ask h j := by
          simp_rw [← mul_assoc, ← Finset.sum_mul]
      _ ≤ (Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)).card *
          2 ^ histCost T ask h j :=
          Nat.mul_le_mul_right _ (children_card_mul_pow_le T b ask j h hlen)

private lemma tr_eq_of_ann_histFlag {n w : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (layer : ZMod 2) (x₀ v : Vec n) (s : ℕ)
    (hv : v ∈ Ann (histFlag ask (tr ask layer x₀ s) s)) :
    ∀ j ≤ s, tr ask layer (x₀ + v) j = tr ask layer x₀ j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hjs
    have hprev : tr ask layer (x₀ + v) j = tr ask layer x₀ j := ih (by omega)
    change step ask layer (x₀ + v) (tr ask layer (x₀ + v) j) = step ask layer x₀ (tr ask layer x₀ j)
    rw [hprev]
    unfold step
    congr 1
    congr 1
    ext i
    have hmono : ∀ r ≤ s, histFlag ask (tr ask layer x₀ s) r ≤ histFlag ask (tr ask layer x₀ s) s := by
      intro r hr
      induction r with
      | zero => exact bot_le
      | succ r _ =>
        have hstep_le : ∀ a b, a ≤ b → histFlag ask (tr ask layer x₀ s) a ≤ histFlag ask (tr ask layer x₀ s) b := by
          intro a b hab
          induction b with
          | zero =>
            have ha0 : a = 0 := by omega
            subst ha0; exact le_rfl
          | succ b ihb =>
            by_cases h : a = b + 1
            · subst h; exact le_rfl
            · exact (ihb (by omega)).trans le_sup_left
        exact hstep_le (r + 1) s hr
    have hmem : (ask (tr ask layer x₀ j) i).1 ∈ histFlag ask (tr ask layer x₀ s) s := by
      have h1 : (ask ((tr ask layer x₀ s).take j) i).1 ∈ histFlag ask (tr ask layer x₀ s) (j + 1) :=
        Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
      rw [tr_take_le ask layer x₀ (by omega : j ≤ s)] at h1
      exact hmono (j + 1) hjs h1
    have hzero : (ask (tr ask layer x₀ j) i).1 v = 0 := hv _ hmem
    rw [map_add, hzero, add_zero]

private lemma histFlag_top_of_injective {n w s : ℕ}
    (ask : List (Fin w → ZMod 2) → Fin w → Dual n × ZMod 2 × ZMod 2)
    (hinj : Function.Injective (fun x : Vec n => tr ask 0 x s))
    (x₀ : Vec n) :
    histFlag ask (tr ask 0 x₀ s) s = ⊤ := by
  by_contra hne
  have hlt : Module.finrank (ZMod 2) (histFlag ask (tr ask 0 x₀ s) s) < n := by
    have hle := finrank_dual_le (histFlag ask (tr ask 0 x₀ s) s)
    by_contra hge
    have heq : Module.finrank (ZMod 2) (histFlag ask (tr ask 0 x₀ s) s) =
        Module.finrank (ZMod 2) (Dual n) := by
      have hd : Module.finrank (ZMod 2) (Dual n) = n := by
        rw [Module.finrank_linearMap, Module.finrank_fin_fun, Module.finrank_self, mul_one]
      omega
    exact hne (Submodule.eq_top_of_finrank_eq heq)
  have hAnn_pos : 0 < Module.finrank (ZMod 2) (Ann (histFlag ask (tr ask 0 x₀ s) s)) := by
    have := finrank_Ann_add_finrank (histFlag ask (tr ask 0 x₀ s) s)
    omega
  have hAnn_ne_bot : Ann (histFlag ask (tr ask 0 x₀ s) s) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hAnn_pos
    omega
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hAnn_ne_bot with ⟨v, hv, hv0⟩
  have htr : tr ask 0 (x₀ + v) s = tr ask 0 x₀ s :=
    tr_eq_of_ann_histFlag ask 0 x₀ v s hv s le_rfl
  have heq : x₀ + v = x₀ := hinj htr
  exact hv0 (add_left_cancel (heq.trans (add_zero x₀).symm))

private noncomputable def spanGenerators {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) : Fin n → Dual n :=
  letI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  let e := Module.finBasis (ZMod 2) M
  fun i => if hi : i.val < Module.finrank (ZMod 2) M then (e ⟨i.val, hi⟩).1 else 0

private lemma span_spanGenerators {n : ℕ} (M : Submodule (ZMod 2) (Dual n)) :
    Submodule.span (ZMod 2) (Set.range (spanGenerators M)) = M := by
  letI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    unfold spanGenerators
    split_ifs with hi
    · exact (Module.finBasis (ZMod 2) M ⟨i.val, hi⟩).2
    · exact M.zero_mem
  · intro φ hφ
    let e := Module.finBasis (ZMod 2) M
    have hle : Module.finrank (ZMod 2) M ≤ n := finrank_dual_le M
    have hrep := e.sum_repr ⟨φ, hφ⟩
    have hval : φ = ∑ k : Fin (Module.finrank (ZMod 2) M), (e.repr ⟨φ, hφ⟩ k) • (e k).1 := by
      have := congrArg Subtype.val hrep
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
    rw [hval]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
    refine Submodule.subset_span ⟨⟨k.val, lt_of_lt_of_le k.isLt hle⟩, ?_⟩
    unfold spanGenerators
    dsimp only
    rw [dif_pos k.isLt]

open Classical in
private noncomputable def askUpTo {n : ℕ} (L : ℕ → Fin n → Dual n)
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) :
    ℕ → (List (Fin n → ZMod 2) → Fin n → Dual n × ZMod 2 × ZMod 2)
  | 0 => fun _ _ => (0, 0, 0)
  | j + 1 =>
    let prev := askUpTo L T b j
    fun h =>
      if h.length = j then
        if hex : ∃ x₀ : Vec n, tr prev 0 x₀ j = h ∧ tr prev 1 (T x₀ + b) j = h then
          let x₀ := Classical.choose hex
          fun i => (L j i, L j i (T x₀ + b) + L j i x₀, 0)
        else
          fun i => (L j i, 0, 0)
      else
        prev h

private lemma askUpTo_agree {n : ℕ} (L : ℕ → Fin n → Dual n)
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) {j m : ℕ} (hjm : j ≤ m)
    (h : List (Fin n → ZMod 2)) (hlen : h.length < j) :
    askUpTo L T b m h = askUpTo L T b j h := by
  induction m with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0; rfl
  | succ m ih =>
    by_cases h' : j = m + 1
    · subst h'; rfl
    · have hne : h.length ≠ m := by omega
      change (if h.length = m then _ else askUpTo L T b m h) = askUpTo L T b j h
      rw [if_neg hne]
      exact ih (by omega)

private lemma tr_askUpTo_agree {n : ℕ} (L : ℕ → Fin n → Dual n)
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) {r j m : ℕ} (hrj : r ≤ j) (hjm : j ≤ m)
    (layer : ZMod 2) (word : Vec n) :
    tr (askUpTo L T b m) layer word r = tr (askUpTo L T b j) layer word r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hprev := ih (by omega)
    change step (askUpTo L T b m) layer word (tr (askUpTo L T b m) layer word r) =
      step (askUpTo L T b j) layer word (tr (askUpTo L T b j) layer word r)
    rw [hprev]
    unfold step
    have hlen : (tr (askUpTo L T b j) layer word r).length < j := by
      rw [tr_length]; omega
    rw [askUpTo_agree L T b hjm _ hlen]

private lemma askUpTo_fst {n : ℕ} (L : ℕ → Fin n → Dual n)
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) {j s : ℕ} (hjs : j < s)
    (h : List (Fin n → ZMod 2)) (hlen : h.length = j) (i : Fin n) :
    (askUpTo L T b s h i).1 = L j i := by
  rw [askUpTo_agree L T b hjs h (by omega)]
  unfold askUpTo
  dsimp only
  rw [if_pos hlen]
  split_ifs <;> rfl

private lemma askUpTo_histFlag {n s : ℕ} (flag : ℕ → Submodule (ZMod 2) (Dual n))
    (h0 : flag 0 = ⊥) (hmono : ∀ j < s, flag j ≤ flag (j + 1))
    (L : ℕ → Fin n → Dual n) (hL : ∀ j < s, Submodule.span (ZMod 2) (Set.range (L j)) = flag (j + 1))
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    {j : ℕ} (hjs : j ≤ s) (h : List (Fin n → ZMod 2)) (hlen : h.length = j) :
    histFlag (askUpTo L T b s) h j = flag j := by
  induction j generalizing h with
  | zero => exact h0.symm
  | succ j ih =>
    have h'len : (h.take j).length = j := by rw [List.length_take, hlen]; omega
    simp only [histFlag]
    rw [histFlag_eq_of_take (askUpTo L T b s) h (h.take j) j (by rw [List.take_take, Nat.min_self]),
      ih (by omega) (h.take j) h'len]
    have hround : roundSpace (askUpTo L T b s) (h.take j) = flag (j + 1) := by
      unfold roundSpace
      have hfun : (fun i : Fin n => (askUpTo L T b s (h.take j) i).1) = L j := by
        funext i
        exact askUpTo_fst L T b (by omega) (h.take j) h'len i
      rw [hfun, hL j (by omega)]
    rw [hround, sup_eq_right.mpr (hmono j (by omega))]

open Classical in
private lemma askUpTo_children_eq {n s : ℕ} (flag : ℕ → Submodule (ZMod 2) (Dual n))
    (h0 : flag 0 = ⊥) (hmono : ∀ j < s, flag j ≤ flag (j + 1))
    (L : ℕ → Fin n → Dual n) (hL : ∀ j < s, Submodule.span (ZMod 2) (Set.range (L j)) = flag (j + 1))
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n)
    {j : ℕ} (hjs : j < s) (h : List (Fin n → ZMod 2)) (hlen : h.length = j) :
    (∑ y : Fin n → ZMod 2,
      (Finset.univ.filter (fun x : Vec n =>
        tr (askUpTo L T b s) 0 x (j + 1) = h ++ [y] ∧
        tr (askUpTo L T b s) 1 (T x + b) (j + 1) = h ++ [y])).card) *
      2 ^ (stepCost T (flag j) (flag (j + 1))) =
    (Finset.univ.filter (fun x : Vec n =>
      tr (askUpTo L T b s) 0 x j = h ∧ tr (askUpTo L T b s) 1 (T x + b) j = h)).card := by
  set ask := askUpTo L T b s
  set Surv := Finset.univ.filter (fun x : Vec n =>
    tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h ∧
    (fun i : Fin n => (ask h i).1 x + (ask h i).2.1 * 0 + (ask h i).2.2) =
    (fun i : Fin n => (ask h i).1 (T x + b) + (ask h i).2.1 * 1 + (ask h i).2.2))
  set Parent := Finset.univ.filter (fun x : Vec n => tr ask 0 x j = h ∧ tr ask 1 (T x + b) j = h)
  have hsum_eq : ∑ y : Fin n → ZMod 2,
      (Finset.univ.filter (fun x : Vec n =>
        tr ask 0 x (j + 1) = h ++ [y] ∧ tr ask 1 (T x + b) (j + 1) = h ++ [y])).card = Surv.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Surv, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
        tr_succ_eq_iff ask 0 x j h hlen, tr_succ_eq_iff ask 1 (T x + b) j h hlen]
      constructor
      · rintro ⟨y, ⟨h0', hy0⟩, ⟨h1', hy1⟩⟩
        exact ⟨h0', h1', hy0.trans hy1.symm⟩
      · rintro ⟨h0', h1', hag⟩
        exact ⟨_, ⟨h0', rfl⟩, ⟨h1', hag.symm⟩⟩
    · intro y₁ _ y₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      have h1 := ((tr_succ_eq_iff ask 0 x j h hlen y₁).mp (Finset.mem_filter.mp hx₁).2.1).2
      have h2 := ((tr_succ_eq_iff ask 0 x j h hlen y₂).mp (Finset.mem_filter.mp hx₂).2.1).2
      exact hne (h1.symm.trans h2)
  rw [hsum_eq]
  by_cases hPne : Parent.Nonempty
  · have hex_prev : ∃ x₀ : Vec n,
        tr (askUpTo L T b j) 0 x₀ j = h ∧ tr (askUpTo L T b j) 1 (T x₀ + b) j = h := by
      rcases hPne with ⟨x, hx⟩
      have hx' := (Finset.mem_filter.mp hx).2
      refine ⟨x, ?_, ?_⟩
      · rw [← tr_askUpTo_agree L T b le_rfl (le_of_lt hjs) 0 x]; exact hx'.1
      · rw [← tr_askUpTo_agree L T b le_rfl (le_of_lt hjs) 1 (T x + b)]; exact hx'.2
    set x₀ := Classical.choose hex_prev
    have hx₀_prev : tr (askUpTo L T b j) 0 x₀ j = h ∧ tr (askUpTo L T b j) 1 (T x₀ + b) j = h :=
      Classical.choose_spec hex_prev
    have hx₀_cur : tr ask 0 x₀ j = h ∧ tr ask 1 (T x₀ + b) j = h := by
      refine ⟨?_, ?_⟩
      · rw [tr_askUpTo_agree L T b le_rfl (le_of_lt hjs) 0 x₀]; exact hx₀_prev.1
      · rw [tr_askUpTo_agree L T b le_rfl (le_of_lt hjs) 1 (T x₀ + b)]; exact hx₀_prev.2
    have hask_h : ask h = fun i => (L j i, L j i (T x₀ + b) + L j i x₀, 0) := by
      change askUpTo L T b s h = _
      rw [askUpTo_agree L T b hjs h (by omega)]
      change (if h.length = j then
        if hex : ∃ x₀ : Vec n, tr (askUpTo L T b j) 0 x₀ j = h ∧ tr (askUpTo L T b j) 1 (T x₀ + b) j = h then
          fun i => (L j i, L j i (T (Classical.choose hex) + b) + L j i (Classical.choose hex), 0)
        else fun i => (L j i, 0, 0)
        else askUpTo L T b j h) = _
      rw [if_pos hlen, dif_pos hex_prev]
    have hx₀_ag : (fun i : Fin n => (ask h i).1 x₀ + (ask h i).2.1 * 0 + (ask h i).2.2) =
        (fun i : Fin n => (ask h i).1 (T x₀ + b) + (ask h i).2.1 * 1 + (ask h i).2.2) := by
      ext i
      rw [hask_h]
      dsimp only
      simp only [mul_zero, add_zero, mul_one]
      have hz := zmod2_add_self (L j i (T x₀ + b))
      calc L j i x₀ = 0 + L j i x₀ := (zero_add _).symm
        _ = (L j i (T x₀ + b) + L j i (T x₀ + b)) + L j i x₀ := by rw [hz]
        _ = L j i (T x₀ + b) + (L j i (T x₀ + b) + L j i x₀) := by ring
    have hflagj : histFlag ask h j = flag j := askUpTo_histFlag flag h0 hmono L hL T b (le_of_lt hjs) h hlen
    have hroundj : roundSpace ask h = flag (j + 1) := by
      unfold roundSpace
      have hfun : (fun i : Fin n => (ask h i).1) = L j := by
        funext i; exact askUpTo_fst L T b hjs h hlen i
      rw [hfun, hL j hjs]
    have hSurv_eq : Surv = Finset.univ.filter (fun x : Vec n =>
        x - x₀ ∈ Ann ((flag j ⊔ (flag j).map (Ddual T)) ⊔ (flag (j + 1)).map (Ddual T))) := by
      ext x
      simp only [Surv, Finset.mem_filter, Finset.mem_univ, true_and]
      have hiff := agree_next_coset_iff T b ask j h hlen x₀ ⟨hx₀_cur.1, hx₀_cur.2, rfl, hx₀_ag⟩ x
      rwa [hflagj, hroundj] at hiff
    have hParent_eq : Parent = Finset.univ.filter (fun x : Vec n =>
        x - x₀ ∈ Ann (flag j ⊔ (flag j).map (Ddual T))) := by
      ext x
      simp only [Parent, Finset.mem_filter, Finset.mem_univ, true_and]
      have hiff := surv_coset_iff T b ask j h hlen x₀ hx₀_cur x
      rwa [hflagj] at hiff
    rw [hSurv_eq, hParent_eq, card_coset_Ann, card_coset_Ann]
    set base := flag j ⊔ (flag j).map (Ddual T)
    change 2 ^ (n - Module.finrank (ZMod 2) (base ⊔ (flag (j + 1)).map (Ddual T) : Submodule (ZMod 2) (Dual n))) *
        2 ^ (Module.finrank (ZMod 2) (base ⊔ (flag (j + 1)).map (Ddual T) : Submodule (ZMod 2) (Dual n)) -
          Module.finrank (ZMod 2) base) =
      2 ^ (n - Module.finrank (ZMod 2) base)
    rw [← pow_add]
    have hle1 : Module.finrank (ZMod 2) base ≤
        Module.finrank (ZMod 2) (base ⊔ (flag (j + 1)).map (Ddual T) : Submodule (ZMod 2) (Dual n)) :=
      Submodule.finrank_mono le_sup_left
    have hle2 : Module.finrank (ZMod 2) (base ⊔ (flag (j + 1)).map (Ddual T) : Submodule (ZMod 2) (Dual n)) ≤ n :=
      finrank_dual_le _
    congr 1
    omega
  · have hP0 : Parent = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPne
    have hS0 : Surv = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      have hmem : x ∈ Parent := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx'.1, hx'.2.1⟩
      rw [hP0] at hmem
      exact Finset.notMem_empty x hmem
    rw [hS0, hP0, Finset.card_empty, zero_mul]

private lemma askUpTo_injective {n s : ℕ} (flag : ℕ → Submodule (ZMod 2) (Dual n))
    (h0 : flag 0 = ⊥) (hs : flag s = ⊤)
    (L : ℕ → Fin n → Dual n) (hL : ∀ j < s, Submodule.span (ZMod 2) (Set.range (L j)) = flag (j + 1))
    (T : Vec n ≃ₗ[ZMod 2] Vec n) (b : Vec n) (layer : ZMod 2) :
    Function.Injective (fun x : Vec n => tr (askUpTo L T b s) layer x s) := by
  intro x y hxy
  by_cases hs0 : s = 0
  · subst hs0
    have hbot_top : (⊥ : Submodule (ZMod 2) (Dual n)) = ⊤ := h0.symm.trans hs
    have hAnn : (⊤ : Submodule (ZMod 2) (Vec n)) = ⊥ := by
      have h1 : Ann (⊥ : Submodule (ZMod 2) (Dual n)) = ⊤ := by
        ext v; simp [Ann]
      rw [← h1, hbot_top, Ann_top_eq_bot]
    have hsub : x - y ∈ (⊥ : Submodule (ZMod 2) (Vec n)) := by
      rw [← hAnn]; exact Submodule.mem_top
    exact sub_eq_zero.mp ((Submodule.mem_bot (ZMod 2)).mp hsub)
  · have hlt : s - 1 < s := by omega
    have hprev : tr (askUpTo L T b s) layer x (s - 1) = tr (askUpTo L T b s) layer y (s - 1) := by
      have ht := congrArg (List.take (s - 1)) hxy
      rwa [tr_take_le _ _ _ (by omega : s - 1 ≤ s), tr_take_le _ _ _ (by omega : s - 1 ≤ s)] at ht
    set h := tr (askUpTo L T b s) layer x (s - 1)
    have hlen : h.length = s - 1 := tr_length _ _ _ _
    have hs_eq : s = (s - 1) + 1 := by omega
    have hxy' : tr (askUpTo L T b s) layer x ((s - 1) + 1) =
        tr (askUpTo L T b s) layer y ((s - 1) + 1) := by
      dsimp only at hxy
      rwa [← hs_eq]
    have hstep_x : tr (askUpTo L T b s) layer x ((s - 1) + 1) =
        h ++ [fun i => (askUpTo L T b s h i).1 x + (askUpTo L T b s h i).2.1 * layer +
          (askUpTo L T b s h i).2.2] := rfl
    have hstep_y : tr (askUpTo L T b s) layer y ((s - 1) + 1) =
        h ++ [fun i => (askUpTo L T b s h i).1 y + (askUpTo L T b s h i).2.1 * layer +
          (askUpTo L T b s h i).2.2] := by
      change tr (askUpTo L T b s) layer y (s - 1) ++ _ = _
      rw [← hprev]
    rw [hstep_x, hstep_y] at hxy'
    have hfun : (fun i => (askUpTo L T b s h i).1 x + (askUpTo L T b s h i).2.1 * layer +
          (askUpTo L T b s h i).2.2) =
        (fun i => (askUpTo L T b s h i).1 y + (askUpTo L T b s h i).2.1 * layer +
          (askUpTo L T b s h i).2.2) :=
      (List.cons.inj (List.append_cancel_left hxy')).1
    have hsub_ann : x - y ∈ Ann (⊤ : Submodule (ZMod 2) (Dual n)) := by
      rw [← hs, hs_eq, ← hL (s - 1) hlt, mem_Ann_span]
      rintro _ ⟨i, rfl⟩
      have heq := congrFun hfun i
      rw [askUpTo_fst L T b hlt h hlen i] at heq
      have hcancel : L (s - 1) i x = L (s - 1) i y := add_right_cancel (add_right_cancel heq)
      rw [map_sub, hcancel, sub_self]
    rw [Ann_top_eq_bot, Submodule.mem_bot] at hsub_ann
    exact sub_eq_zero.mp hsub_ann

end PEqualNP.Outside.L_pcx_380

theorem PEqualNP.Outside.L_pcx_380 :
    ∀ (n s : ℕ),
      let V := Fin n → ZMod 2
      let U := V →ₗ[ZMod 2] ZMod 2
      let transcript := fun (w : ℕ)
          (ask : List (Fin w → ZMod 2) → Fin w → U × ZMod 2 × ZMod 2)
          (layer : ZMod 2) (word : V) =>
        (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
          hist ++ [fun i : Fin w => (ask hist i).1 word + (ask hist i).2.1 * layer + (ask hist i).2.2]) []
      ∀ (T : V ≃ₗ[ZMod 2] V) (b : V),
        let feasible := fun K : ℕ =>
          ∃ (w : ℕ) (ask : List (Fin w → ZMod 2) → Fin w → U × ZMod 2 × ZMod 2),
            (∀ layer : ZMod 2, Function.Injective (transcript w ask layer)) ∧
            K ≤ (Finset.univ.filter (fun x : V =>
              transcript w ask 0 x = transcript w ask 1 (T x + b))).card
        let shift := fun S : Submodule (ZMod 2) U =>
          Submodule.span (ZMod 2) (Set.image (fun a : U => a.comp T.toLinearMap + a) (S : Set U))
        ∀ K : ℕ, feasible K ↔
          ∃ flag : ℕ → Submodule (ZMod 2) U,
            flag 0 = ⊥ ∧ flag s = ⊤ ∧ (∀ j < s, flag j ≤ flag (j+1)) ∧
            K * 2 ^ ((Finset.range s).sum (fun j =>
              let base := flag j ⊔ shift (flag j)
              Module.finrank (ZMod 2) (base ⊔ shift (flag (j+1)) : Submodule (ZMod 2) U) - Module.finrank (ZMod 2) base)) ≤ 2 ^ n := by
  intro n s
  dsimp only
  intro T b K
  have hshift_eq : ∀ S : Submodule (ZMod 2) (PEqualNP.Outside.L_pcx_380.Dual n),
      Submodule.span (ZMod 2) (Set.image (fun a => a.comp T.toLinearMap + a) (S : Set _)) =
        S.map (PEqualNP.Outside.L_pcx_380.Ddual T) :=
    PEqualNP.Outside.L_pcx_380.shift_eq_map T
  constructor
  · rintro ⟨w, ask, hinj, hK⟩
    have htr_eq : ∀ layer x,
        (List.range s).foldl (fun (hist : List (Fin w → ZMod 2)) (_ : ℕ) =>
          hist ++ [fun i : Fin w => (ask hist i).1 x + (ask hist i).2.1 * layer + (ask hist i).2.2]) [] =
        PEqualNP.Outside.L_pcx_380.tr ask layer x s :=
      fun layer x => PEqualNP.Outside.L_pcx_380.tr_eq_foldl ask layer x s
    have hinj0 : Function.Injective (fun x => PEqualNP.Outside.L_pcx_380.tr ask 0 x s) := by
      intro x y hxy
      apply hinj 0
      dsimp only
      rwa [htr_eq 0 x, htr_eq 0 y]
    by_cases hK0 : K = 0
    · subst hK0
      set h₀ := PEqualNP.Outside.L_pcx_380.tr ask 0 0 s
      refine ⟨PEqualNP.Outside.L_pcx_380.histFlag ask h₀, rfl,
        PEqualNP.Outside.L_pcx_380.histFlag_top_of_injective ask hinj0 0,
        fun j _ => le_sup_left, by simp⟩
    · classical
      set Matches := Finset.univ.filter (fun x : Fin n → ZMod 2 =>
        PEqualNP.Outside.L_pcx_380.tr ask 0 x s =
          PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) s)
      have hK_le : K ≤ Matches.card := by
        convert hK using 2
        ext x
        simp only [Matches, Finset.mem_filter, Finset.mem_univ, true_and, htr_eq]
      set Occ := (PEqualNP.Outside.L_pcx_380.Hists w s).filter (fun h =>
        (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
          PEqualNP.Outside.L_pcx_380.tr ask 0 x s = h ∧
          PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) s = h)).Nonempty)
      have hMatches_sum : Matches.card = ∑ h ∈ Occ,
          (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
            PEqualNP.Outside.L_pcx_380.tr ask 0 x s = h ∧
            PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) s = h)).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext x
          simp only [Matches, Occ, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            PEqualNP.Outside.L_pcx_380.mem_Hists_iff]
          constructor
          · intro hmatch
            refine ⟨PEqualNP.Outside.L_pcx_380.tr ask 0 x s,
              ⟨PEqualNP.Outside.L_pcx_380.tr_length ask 0 x s,
                ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl, hmatch.symm⟩⟩⟩,
              rfl, hmatch.symm⟩
          · rintro ⟨h, _, h0, h1⟩
            exact h0.trans h1.symm
        · intro h₁ _ h₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          exact hne ((Finset.mem_filter.mp hx₁).2.1.symm.trans (Finset.mem_filter.mp hx₂).2.1)
      have hOcc_ne : Occ.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hMatches_sum
        omega
      rcases Finset.exists_min_image Occ (fun h => PEqualNP.Outside.L_pcx_380.histCost T ask h s) hOcc_ne
        with ⟨h_star, hh_star_mem, hh_star_min⟩
      have hpow_le : K * 2 ^ (PEqualNP.Outside.L_pcx_380.histCost T ask h_star s) ≤ 2 ^ n := by
        calc K * 2 ^ PEqualNP.Outside.L_pcx_380.histCost T ask h_star s
            ≤ Matches.card * 2 ^ PEqualNP.Outside.L_pcx_380.histCost T ask h_star s :=
              Nat.mul_le_mul_right _ hK_le
          _ = ∑ h ∈ Occ,
                (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
                  PEqualNP.Outside.L_pcx_380.tr ask 0 x s = h ∧
                  PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) s = h)).card *
                2 ^ PEqualNP.Outside.L_pcx_380.histCost T ask h_star s := by
              rw [hMatches_sum, Finset.sum_mul]
          _ ≤ ∑ h ∈ Occ,
                (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
                  PEqualNP.Outside.L_pcx_380.tr ask 0 x s = h ∧
                  PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) s = h)).card *
                2 ^ PEqualNP.Outside.L_pcx_380.histCost T ask h s := by
              refine Finset.sum_le_sum (fun h hh => Nat.mul_le_mul_left _ ?_)
              exact Nat.pow_le_pow_right (by omega) (hh_star_min h hh)
          _ ≤ ∑ h ∈ PEqualNP.Outside.L_pcx_380.Hists w s,
                (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
                  PEqualNP.Outside.L_pcx_380.tr ask 0 x s = h ∧
                  PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) s = h)).card *
                2 ^ PEqualNP.Outside.L_pcx_380.histCost T ask h s :=
              Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
          _ ≤ 2 ^ n := PEqualNP.Outside.L_pcx_380.weighted_sum_le T b ask s
      rcases (Finset.mem_filter.mp hh_star_mem).2 with ⟨x₀, hx₀⟩
      have hx₀_tr : PEqualNP.Outside.L_pcx_380.tr ask 0 x₀ s = h_star :=
        (Finset.mem_filter.mp hx₀).2.1
      refine ⟨PEqualNP.Outside.L_pcx_380.histFlag ask h_star, rfl, ?_, fun j _ => le_sup_left, ?_⟩
      · rw [← hx₀_tr]
        exact PEqualNP.Outside.L_pcx_380.histFlag_top_of_injective ask hinj0 x₀
      · have hCeq : (Finset.range s).sum (fun j =>
            let base := PEqualNP.Outside.L_pcx_380.histFlag ask h_star j ⊔
              Submodule.span (ZMod 2) (Set.image (fun a => a.comp T.toLinearMap + a)
                (PEqualNP.Outside.L_pcx_380.histFlag ask h_star j : Set _))
            Module.finrank (ZMod 2) (base ⊔
              Submodule.span (ZMod 2) (Set.image (fun a => a.comp T.toLinearMap + a)
                (PEqualNP.Outside.L_pcx_380.histFlag ask h_star (j + 1) : Set _)) : Submodule (ZMod 2) _) -
              Module.finrank (ZMod 2) base) =
            PEqualNP.Outside.L_pcx_380.histCost T ask h_star s := by
          rw [PEqualNP.Outside.L_pcx_380.histCost_eq_range_sum T ask h_star s]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          dsimp only [PEqualNP.Outside.L_pcx_380.stepCost]
          rw [hshift_eq, hshift_eq]
        rw [hCeq]
        exact hpow_le
  · rintro ⟨flag, hflag0, hflags, hmono, hKbound⟩
    classical
    let L : ℕ → Fin n → PEqualNP.Outside.L_pcx_380.Dual n :=
      fun j => PEqualNP.Outside.L_pcx_380.spanGenerators (flag (j + 1))
    have hL : ∀ j < s, Submodule.span (ZMod 2) (Set.range (L j)) = flag (j + 1) :=
      fun j _ => PEqualNP.Outside.L_pcx_380.span_spanGenerators (flag (j + 1))
    let ask := PEqualNP.Outside.L_pcx_380.askUpTo L T b s
    refine ⟨n, ask, ?_, ?_⟩
    · intro layer x y hxy
      dsimp only at hxy
      rw [PEqualNP.Outside.L_pcx_380.tr_eq_foldl ask layer x s,
        PEqualNP.Outside.L_pcx_380.tr_eq_foldl ask layer y s] at hxy
      exact PEqualNP.Outside.L_pcx_380.askUpTo_injective flag hflag0 hflags L hL T b layer hxy
    · have hsum_exact : ∀ j ≤ s,
          (∑ h ∈ PEqualNP.Outside.L_pcx_380.Hists n j,
            (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
              PEqualNP.Outside.L_pcx_380.tr ask 0 x j = h ∧
              PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) j = h)).card) *
            2 ^ ((Finset.range j).sum (fun r =>
              PEqualNP.Outside.L_pcx_380.stepCost T (flag r) (flag (r + 1)))) = 2 ^ n := by
        intro j
        induction j with
        | zero =>
          intro _
          simp only [PEqualNP.Outside.L_pcx_380.Hists, Finset.sum_singleton, Finset.range_zero,
            Finset.sum_empty, pow_zero, mul_one, PEqualNP.Outside.L_pcx_380.tr, true_and,
            Finset.filter_true, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
            ZMod.card 2, Finset.prod_const]
        | succ j ih =>
          intro hjs
          rw [PEqualNP.Outside.L_pcx_380.sum_Hists_succ, Finset.sum_range_succ, pow_add]
          calc (∑ h ∈ PEqualNP.Outside.L_pcx_380.Hists n j,
                  ∑ y : Fin n → ZMod 2,
                    (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
                      PEqualNP.Outside.L_pcx_380.tr ask 0 x (j + 1) = h ++ [y] ∧
                      PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
                (2 ^ ((Finset.range j).sum (fun r =>
                  PEqualNP.Outside.L_pcx_380.stepCost T (flag r) (flag (r + 1)))) *
                2 ^ PEqualNP.Outside.L_pcx_380.stepCost T (flag j) (flag (j + 1)))
              = ((∑ h ∈ PEqualNP.Outside.L_pcx_380.Hists n j,
                  ∑ y : Fin n → ZMod 2,
                    (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
                      PEqualNP.Outside.L_pcx_380.tr ask 0 x (j + 1) = h ++ [y] ∧
                      PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
                  2 ^ PEqualNP.Outside.L_pcx_380.stepCost T (flag j) (flag (j + 1))) *
                2 ^ ((Finset.range j).sum (fun r =>
                  PEqualNP.Outside.L_pcx_380.stepCost T (flag r) (flag (r + 1)))) := by ring
            _ = (∑ h ∈ PEqualNP.Outside.L_pcx_380.Hists n j,
                  (∑ y : Fin n → ZMod 2,
                    (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
                      PEqualNP.Outside.L_pcx_380.tr ask 0 x (j + 1) = h ++ [y] ∧
                      PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) (j + 1) = h ++ [y])).card) *
                  2 ^ PEqualNP.Outside.L_pcx_380.stepCost T (flag j) (flag (j + 1))) *
                2 ^ ((Finset.range j).sum (fun r =>
                  PEqualNP.Outside.L_pcx_380.stepCost T (flag r) (flag (r + 1)))) := by
                rw [Finset.sum_mul]
            _ = (∑ h ∈ PEqualNP.Outside.L_pcx_380.Hists n j,
                  (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
                    PEqualNP.Outside.L_pcx_380.tr ask 0 x j = h ∧
                    PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) j = h)).card) *
                2 ^ ((Finset.range j).sum (fun r =>
                  PEqualNP.Outside.L_pcx_380.stepCost T (flag r) (flag (r + 1)))) := by
                congr 1
                refine Finset.sum_congr rfl (fun h hh => ?_)
                exact PEqualNP.Outside.L_pcx_380.askUpTo_children_eq flag hflag0 hmono L hL T b
                  (by omega) h (PEqualNP.Outside.L_pcx_380.mem_Hists_iff.mp hh)
            _ = 2 ^ n := ih (by omega)
      have hMatches_eq :
          (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
            (List.range s).foldl (fun (hist : List (Fin n → ZMod 2)) (_ : ℕ) =>
              hist ++ [fun i : Fin n => (ask hist i).1 x + (ask hist i).2.1 * 0 + (ask hist i).2.2]) [] =
            (List.range s).foldl (fun (hist : List (Fin n → ZMod 2)) (_ : ℕ) =>
              hist ++ [fun i : Fin n => (ask hist i).1 (T x + b) + (ask hist i).2.1 * 1 + (ask hist i).2.2]) [])).card =
          ∑ h ∈ PEqualNP.Outside.L_pcx_380.Hists n s,
            (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
              PEqualNP.Outside.L_pcx_380.tr ask 0 x s = h ∧
              PEqualNP.Outside.L_pcx_380.tr ask 1 (T x + b) s = h)).card := by
        rw [← Finset.card_biUnion]
        · congr 1
          ext x
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            PEqualNP.Outside.L_pcx_380.mem_Hists_iff, PEqualNP.Outside.L_pcx_380.tr_eq_foldl]
          constructor
          · intro hmatch
            exact ⟨PEqualNP.Outside.L_pcx_380.tr ask 0 x s,
              PEqualNP.Outside.L_pcx_380.tr_length ask 0 x s, rfl, hmatch.symm⟩
          · rintro ⟨h, _, h0, h1⟩
            exact h0.trans h1.symm
        · intro h₁ _ h₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro x hx₁ hx₂
          exact hne ((Finset.mem_filter.mp hx₁).2.1.symm.trans (Finset.mem_filter.mp hx₂).2.1)
      have hC_eq : (Finset.range s).sum (fun j =>
          let base := flag j ⊔ Submodule.span (ZMod 2) (Set.image (fun a => a.comp T.toLinearMap + a) (flag j : Set _))
          Module.finrank (ZMod 2) (base ⊔ Submodule.span (ZMod 2) (Set.image (fun a => a.comp T.toLinearMap + a) (flag (j + 1) : Set _)) : Submodule (ZMod 2) _) -
            Module.finrank (ZMod 2) base) =
          (Finset.range s).sum (fun j => PEqualNP.Outside.L_pcx_380.stepCost T (flag j) (flag (j + 1))) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        dsimp only [PEqualNP.Outside.L_pcx_380.stepCost]
        rw [hshift_eq (flag j), hshift_eq (flag (j + 1))]
      rw [hC_eq] at hKbound
      have hexact := hsum_exact s le_rfl
      rw [← hMatches_eq] at hexact
      have hmul : K * 2 ^ ((Finset.range s).sum (fun r =>
          PEqualNP.Outside.L_pcx_380.stepCost T (flag r) (flag (r + 1)))) ≤
          (Finset.univ.filter (fun x : Fin n → ZMod 2 =>
            (List.range s).foldl (fun (hist : List (Fin n → ZMod 2)) (_ : ℕ) =>
              hist ++ [fun i : Fin n => (ask hist i).1 x + (ask hist i).2.1 * 0 + (ask hist i).2.2]) [] =
            (List.range s).foldl (fun (hist : List (Fin n → ZMod 2)) (_ : ℕ) =>
              hist ++ [fun i : Fin n => (ask hist i).1 (T x + b) + (ask hist i).2.1 * 1 + (ask hist i).2.2]) [])).card *
          2 ^ ((Finset.range s).sum (fun r =>
            PEqualNP.Outside.L_pcx_380.stepCost T (flag r) (flag (r + 1)))) := by
        rw [hexact]
        exact hKbound
      exact Nat.le_of_mul_le_mul_right hmul (Nat.pos_of_ne_zero (by positivity))
